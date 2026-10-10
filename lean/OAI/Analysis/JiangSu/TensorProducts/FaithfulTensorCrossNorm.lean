import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRescaling
import OAI.Analysis.JiangSu.CStarAlgebras.CStarNormCompletion

namespace OAI

noncomputable section
namespace NuclearUnitization
open scoped CStarAlgebra TensorProduct

lemma rectangle_bound {a b c : ℝ} (_ha : 0≤a) (hb : 0≤b) (hc : 0≤c)
    (h : ∀ x y, 0<x → x<a → 0<y → y<b → x*y≤c) : a*b≤c := by
  by_cases ha0 : a=0
  · simpa [ha0] using hc
  by_cases hb0 : b=0
  · simpa [hb0] using hc
  have hbp : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  apply le_of_forall_lt
  intro r hr
  by_cases hr0 : r<0
  · exact hr0.trans_le hc
  have hr0' : 0≤r := le_of_not_gt hr0
  have hdiv : r/b<a := (div_lt_iff₀ hbp).mpr (by simpa [mul_comm] using hr)
  obtain ⟨x,hx0,hxa⟩ := exists_between hdiv
  have hx : 0<x := (div_nonneg hr0' hbp.le).trans_lt hx0
  have hrx : r/x<b := (div_lt_iff₀ hx).mpr (by
    have hh := (div_lt_iff₀ hbp).mp hx0
    simpa [mul_comm] using hh)
  obtain ⟨y,hy0,hyb⟩ := exists_between hrx
  have hy : 0<y := (div_nonneg hr0' hx.le).trans_lt hy0
  exact ((div_lt_iff₀ hx).mp hy0).trans_le (by simpa [mul_comm] using h x y hx hxa hy hyb)

variable {A B N : Type*} [CStarAlgebra A] [CStarAlgebra B] [NonUnitalCStarAlgebra N]
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
variable [PartialOrder N] [StarOrderedRing N]

def cut (a : A) (r : ℝ) : A := cfc (fun t : ℝ => max (t-r) 0) a

lemma cut_nonneg (a : A) (r : ℝ) : 0≤cut a r := by
  exact cfc_nonneg (fun t _ => le_max_right _ _)

lemma cut_nonzero [Nontrivial A] {a : A} (ha : 0≤a) {r : ℝ} (hr : r<‖a‖) : cut a r≠0 := by
  intro hz
  have hfun : cfc (fun t : ℝ => max (t-r) 0) a=cfc (fun _ : ℝ => 0) a := by
    simpa only [cut,cfc_const_zero] using hz
  have h := eqOn_of_cfc_eq_cfc hfun (ha := ha.isSelfAdjoint)
  specialize h (x := ‖a‖) (CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)
  have hp : 0 < max (‖a‖-r) 0 := lt_max_of_lt_left (sub_pos.mpr hr)
  exact (ne_of_gt hp) h

lemma cut_lower (a : A) (ha : 0≤a) (r : ℝ) : r • cut a r≤a*cut a r := by
  change r • cfc (fun t : ℝ => max (t-r) 0) a≤a*cfc (fun t : ℝ => max (t-r) 0) a
  rw [←cfc_smul r (fun t : ℝ => max (t-r) 0) a]
  nth_rw 2 [←cfc_id' ℝ a]
  rw [←cfc_mul (fun t : ℝ => t) (fun t : ℝ => max (t-r) 0) a]
  apply (cfc_le_iff _ _ a (ha := ha.isSelfAdjoint)).mpr
  intro t ht
  change r*max (t-r) 0≤t*max (t-r) 0
  by_cases htr : r≤t
  · exact mul_le_mul_of_nonneg_right htr (le_max_right _ _)
  · rw [max_eq_right (by linarith : t-r≤0)]
    simp

lemma commute_mul_le_mul_of_nonneg_right {x y z : N} (hxy : x≤y) (hz : 0≤z)
    (hxz : Commute x z) (hyz : Commute y z) : x*z≤y*z := by
  rw [←sub_nonneg,←sub_mul]
  exact Commute.mul_nonneg (sub_nonneg.mpr hxy) hz (hyz.sub_left hxz)

lemma faithful_pair_positive_norm (φ : A →⋆ₙₐ[ℂ] N) (ψ : B →⋆ₙₐ[ℂ] N)
    (hc : ∀ a b,Commute (φ a) (ψ b))
    (hind : ∀ a b,a≠0 → b≠0 → φ a*ψ b≠0)
    (a : A) (b : B) (ha : 0≤a) (hb : 0≤b) : ‖φ a*ψ b‖=‖a‖*‖b‖ := by
  apply le_antisymm
  · exact (norm_mul_le _ _).trans (mul_le_mul
      (NonUnitalStarAlgHom.norm_apply_le φ a) (NonUnitalStarAlgHom.norm_apply_le ψ b)
      (norm_nonneg _) (norm_nonneg _))
  by_cases hAt : Subsingleton A
  · simp [Subsingleton.elim a 0]
  by_cases hBt : Subsingleton B
  · simp [Subsingleton.elim b 0]
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hAt
  let : Nontrivial B := not_subsingleton_iff_nontrivial.mp hBt
  apply rectangle_bound (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  intro r s hr hra hs hsb
  let x := φ (cut a r)
  let y := ψ (cut b s)
  have hxp : 0≤x := map_nonneg φ (cut_nonneg a r)
  have hyp : 0≤y := map_nonneg ψ (cut_nonneg b s)
  have hxy : Commute x y := hc _ _
  have hp : 0≤x*y := Commute.mul_nonneg hxp hyp hxy
  have hn0 : 0<‖x*y‖ := norm_pos_iff.mpr (hind _ _ (cut_nonzero ha hra) (cut_nonzero hb hsb))
  have hxa : Commute x (φ a) := by
    exact (Commute.refl a).cfc_real (fun t : ℝ => max (t-r) 0) |>.map φ
  have hyb : Commute y (ψ b) := by
    exact (Commute.refl b).cfc_real (fun t : ℝ => max (t-s) 0) |>.map ψ
  have hxlow : r • x≤φ a*x := by
    simpa only [map_smul,map_mul,NonUnitalStarAlgHom.restrictScalars_apply,x] using OrderHomClass.mono (φ.restrictScalars ℝ) (cut_lower a ha r)
  have hylow : s • y≤ψ b*y := by
    simpa only [map_smul,map_mul,NonUnitalStarAlgHom.restrictScalars_apply,y] using OrderHomClass.mono (ψ.restrictScalars ℝ) (cut_lower b hb s)
  have h1 : r • (x*y)≤φ a*x*y := by
    simpa only [smul_mul_assoc] using commute_mul_le_mul_of_nonneg_right hxlow hyp
      (hxy.smul_left r) ((hc a (cut b s)).mul_left hxy)
  have h2 : s • (φ a*x*y)≤φ a*x*(ψ b*y) := by
    have haxp : 0≤φ a*x := Commute.mul_nonneg
      (map_nonneg φ ha) hxp hxa.symm
    have hcom : Commute (φ a*x) y := (hc _ _).mul_left hxy
    have hcomb : Commute (φ a*x) (ψ b) := (hc _ _).mul_left (hc _ _)
    have ht := commute_mul_le_mul_of_nonneg_right hylow haxp
      (hcom.symm.smul_left s) (hcomb.symm.mul_left hcom.symm)
    rw [smul_mul_assoc, hcom.symm.eq, ((hcomb.mul_right hcom).symm).eq] at ht
    exact ht
  have h3 : (r*s) • (x*y)≤(φ a*ψ b)*(x*y) := by
    have ht := (smul_le_smul_of_nonneg_left h1 hs.le).trans h2
    have he : φ a*x*(ψ b*y)=(φ a*ψ b)*(x*y) := by
      rw [mul_assoc,←mul_assoc x, (hc (cut a r) b).eq]
      noncomm_ring
    simpa [smul_smul,mul_comm r s,he] using ht
  have ht := CStarAlgebra.norm_le_norm_of_le_of_nonneg h3
    (smul_nonneg (mul_nonneg hr.le hs.le) hp)
  have ht' := ht.trans (norm_mul_le (φ a*ψ b) (x*y))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le hs.le)] at ht'
  exact (mul_le_mul_iff_left₀ hn0).mp ht'

lemma faithful_pair_norm (φ : A →⋆ₙₐ[ℂ] N) (ψ : B →⋆ₙₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b))
    (hind : ∀ a b, a≠0 → b≠0 → φ a*ψ b≠0)
    (a : A) (b : B) : ‖φ a*ψ b‖=‖a‖*‖b‖ := by
  have he : star (φ a*ψ b)*(φ a*ψ b) = φ (star a*a)*ψ (star b*b) := by
    rw [star_mul,←map_star,←map_star]
    calc
      ψ (star b)*φ (star a)*(φ a*ψ b) = ψ (star b)*(φ (star a*a)*ψ b) := by
        simp only [map_mul,mul_assoc]
      _ = φ (star a*a)*(ψ (star b)*ψ b) := by
        rw [←mul_assoc,(hc (star a*a) (star b)).symm.eq,mul_assoc]
      _ = _ := by simp only [map_mul]
  have hn := faithful_pair_positive_norm φ ψ hc hind (star a*a) (star b*b)
    (star_mul_self_nonneg _) (star_mul_self_nonneg _)
  rw [←he,CStarRing.norm_star_mul_self,CStarRing.norm_star_mul_self,
    CStarRing.norm_star_mul_self] at hn
  apply (mul_self_inj_of_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mp
  nlinarith only [hn]

end NuclearUnitization

namespace NuclearUnitization
open Pureness
open scoped TensorProduct CStarAlgebra

lemma tmul_nonzero {A B : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] {a : A} {b : B} (ha : a≠0) (hb : b≠0) :
    a ⊗ₜ[ℂ] b≠0 := by
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  intro hz
  have hh := congrArg (fun z => TensorProduct.lid ℂ B (TensorProduct.map f (LinearMap.id : B →ₗ[ℂ] B) z)) hz
  simp only [TensorProduct.map_tmul,LinearMap.id_apply,TensorProduct.lid_tmul,hf,one_smul,map_zero] at hh
  exact hb hh

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

private def leftMap (p : CStarAlgebraNorm (A ⊗[ℂ] B)) : A →⋆ₙₐ[ℂ] p.Completion where
  toFun a := p.completionMap (a ⊗ₜ[ℂ] (1 : B))
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.add_tmul]
  map_smul' z a := by
    rw [←TensorProduct.smul_tmul']
    exact p.completionMap.map_smul z _
  map_mul' a b := by rw [←map_mul]; simp
  map_star' a := by rw [←map_star]; simp

private def rightMap (p : CStarAlgebraNorm (A ⊗[ℂ] B)) : B →⋆ₙₐ[ℂ] p.Completion where
  toFun b := p.completionMap ((1 : A) ⊗ₜ[ℂ] b)
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add]
  map_smul' z a := by
    rw [TensorProduct.tmul_smul]
    exact p.completionMap.map_smul z _
  map_mul' a b := by rw [←map_mul]; simp
  map_star' a := by rw [←map_star]; simp

lemma cstar_norm_tmul (p : CStarAlgebraNorm (A ⊗[ℂ] B)) (a : A) (b : B) :
    p.toAlgebraNorm (a ⊗ₜ[ℂ] b)=‖a‖*‖b‖ := by
  have hm (a : A) (b : B) : leftMap p a*rightMap p b=p.completionMap (a ⊗ₜ[ℂ] b) := by
    change p.completionMap (a ⊗ₜ[ℂ] 1)*p.completionMap (1 ⊗ₜ[ℂ] b)=_
    rw [←map_mul]; simp
  have hc (a : A) (b : B) : Commute (leftMap p a) (rightMap p b) := by
    change Commute (p.completionMap (a ⊗ₜ[ℂ] 1)) (p.completionMap (1 ⊗ₜ[ℂ] b))
    exact ((Commute.one_right a).tmul (Commute.one_left b)).map p.completionMap
  have hi (a : A) (b : B) (ha : a≠0) (hb : b≠0) : leftMap p a*rightMap p b≠0 := by
    rw [hm]
    exact fun h => tmul_nonzero ha hb (p.completionMap_injective (by simpa using h))
  rw [←p.completionMap_norm,←hm]
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : PartialOrder p.Completion := CStarAlgebra.spectralOrder p.Completion
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : StarOrderedRing p.Completion := CStarAlgebra.spectralOrderedRing p.Completion
  exact faithful_pair_norm (leftMap p) (rightMap p) hc hi a b

end NuclearUnitization

end

end OAI
