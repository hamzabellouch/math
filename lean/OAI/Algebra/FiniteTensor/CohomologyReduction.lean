import Mathlib

namespace OAI

/-! Cohomology projections, contractions and finite tensor-cycle reduction. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 
theorem exists_retraction_preserving (U W : Submodule K V) :
    ∃ q : V →ₗ[K] U,
      (∀ u : U, q u = u) ∧ (∀ w ∈ W, (q w : V) ∈ W) := by
  obtain ⟨D, hD, heq⟩ := IsModularLattice.exists_disjoint_and_sup_eq (show U ⊓ W ≤ W from inf_le_right)
  have hDW : D ≤ W := by rw [← heq]; exact le_sup_right
  have hUD : Disjoint U D := by
    apply Submodule.disjoint_def.mpr
    intro x hxU hxD
    exact Submodule.disjoint_def.mp hD x ⟨hxU, hDW hxD⟩ hxD
  obtain ⟨Q, hDQ, hUQ⟩ := hUD.symm.exists_isCompl
  have hUQ := hUQ.symm
  refine ⟨U.projectionOnto Q hUQ, Submodule.projectionOnto_apply_left hUQ, ?_⟩
  intro w hw
  rw [← heq, Submodule.mem_sup] at hw
  obtain ⟨u, hu, d, hd, rfl⟩ := hw
  rw [map_add, Submodule.projectionOnto_apply_of_mem_left hUQ hu.1,
    Submodule.projectionOnto_apply_of_mem_right hUQ (hDQ hd), add_zero]
  exact hu.2

 

theorem exists_cohomology_projection (B Z W : Submodule K V) (hBZ : B ≤ Z) :
    ∃ p : V →ₗ[K] V,
      (∀ v, p v ∈ Z) ∧
      (∀ b ∈ B, p b = 0) ∧
      (∀ z ∈ Z, z - p z ∈ B) ∧
      (∀ w ∈ W, p w ∈ W) ∧
      p.comp p = p := by
  obtain ⟨q, hqZ, hqW⟩ := exists_retraction_preserving Z W
  let B' : Submodule K Z := B.comap Z.subtype
  let W' : Submodule K Z := W.comap Z.subtype
  obtain ⟨r, hrB, hrW⟩ := exists_retraction_preserving B' W'
  let s : Z →ₗ[K] Z := LinearMap.id - B'.subtype.comp r
  let p : V →ₗ[K] V := Z.subtype.comp (s.comp q)
  have hpval (v : V) : p v = (q v : V) - ((r (q v) : Z) : V) := rfl
  have hpZ (v : V) : p v ∈ Z := (s (q v)).property
  have hpB (b : V) (hb : b ∈ B) : p b = 0 := by
    have hq : q b = ⟨b, hBZ hb⟩ := hqZ ⟨b, hBZ hb⟩
    rw [hpval, hq]
    have hr := hrB (⟨⟨b, hBZ hb⟩, hb⟩ : B')
    dsimp at hr
    rw [hr]
    simp
  have hpmod (z : V) (hz : z ∈ Z) : z - p z ∈ B := by
    have hq : q z = ⟨z, hz⟩ := hqZ ⟨z, hz⟩
    rw [hpval, hq]
    convert (show ((r ⟨z, hz⟩ : Z) : V) ∈ B from (r ⟨z, hz⟩).property) using 1; abel
  have hpW (w : V) (hw : w ∈ W) : p w ∈ W := by
    rw [hpval]
    apply W.sub_mem (hqW w hw)
    exact hrW (q w) (hqW w hw)
  refine ⟨p, hpZ, hpB, hpmod, hpW, ?_⟩
  ext v
  have h := hpB ((q v : V) - p (q v)) (hpmod (q v) (q v).property)
  simp only [map_sub, sub_eq_zero] at h
  have hq : p (q v) = p v := by
    dsimp only [p, LinearMap.comp_apply]
    rw [hqZ]
  simpa only [LinearMap.comp_apply, hq] using h.symm

 

theorem exists_even_cohomology_projection [Invertible (2 : K)]
    (B Z W : Submodule K V) (hBZ : B ≤ Z) (g : V →ₗ[K] V)
    (hg : ∀ v, g (g v) = v)
    (hgB : ∀ b∈B, g b∈B) (hgZ : ∀ z∈Z, g z∈Z) (hgW : ∀ w∈W, g w∈W) :
    ∃ p : V →ₗ[K] V,
      (∀ v, p v∈Z) ∧ (∀ b∈B, p b=0) ∧ (∀ z∈Z, z-p z∈B) ∧
      (∀ w∈W, p w∈W) ∧ p.comp p=p ∧ p.comp g = g.comp p := by
  obtain ⟨p, hpZ, hpB, hpmod, hpW, _⟩ := exists_cohomology_projection B Z W hBZ
  let c : K := (2 : K)⁻¹
  have hc : c+c=1 := by
    dsimp [c]
    rw [← mul_two, inv_mul_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero]
  let q : V →ₗ[K] V := c • (p + g.comp (p.comp g))
  have hq (v : V) : q v = c • (p v + g (p (g v))) := rfl
  have hqZ (v : V) : q v∈Z := by
    rw [hq]; exact Z.smul_mem c (Z.add_mem (hpZ v) (hgZ _ (hpZ _)))
  have hqB (b : V) (hb : b∈B) : q b=0 := by
    rw [hq, hpB b hb, hpB (g b) (hgB b hb)]; simp
  have hqW (w : V) (hw : w∈W) : q w∈W := by
    rw [hq]; exact W.smul_mem c (W.add_mem (hpW w hw) (hgW _ (hpW _ (hgW w hw))))
  have hqg (v : V) : q (g v) = g (q v) := by
    simp only [hq, hg, map_smul, map_add]
    rw [add_comm]
  have hqmod (z : V) (hz : z∈Z) : z-q z∈B := by
    have h := B.smul_mem c (B.add_mem (hpmod z hz)
      (hgB _ (hpmod (g z) (hgZ z hz))))
    have heq : c • ((z-p z) + g (g z-p (g z))) = z-q z := by
      simp only [map_sub, hg, hq, smul_add, smul_sub]
      calc
        c • z - c • p z + (c • z - c • g (p (g z))) =
            (c+c) • z - (c • p z+c • g (p (g z))) := by rw [add_smul]; abel
        _ = _ := by rw [hc, one_smul]
    rwa [heq] at h
  have hqcycle (z : V) (hz : z∈Z) : q (q z) = q z := by
    have h := hqB (z-q z) (hqmod z hz)
    rw [map_sub] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨q.comp q, fun v => hqZ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; simp [hqB b hb]
  · intro z hz
    simpa only [LinearMap.comp_apply, hqcycle z hz] using hqmod z hz
  · intro w hw; exact hqW _ (hqW w hw)
  · ext v
    simp only [LinearMap.comp_apply, hqcycle (q v) (hqZ v)]
  · ext v
    simp only [LinearMap.comp_apply, hqg]

 

theorem exists_contraction (δ p : V →ₗ[K] V)
    (hδ : ∀ v, δ (δ v) = 0)
    (hpZ : ∀ v, δ (p v) = 0)
    (hpB : ∀ v, p (δ v) = 0)
    (hpmod : ∀ z, δ z=0 → z-p z∈LinearMap.range δ)
    (hpp : ∀ v, p (p v)= p v) :
    ∃ h : V →ₗ[K] V, ∀ v, δ (h v) + h (δ v) = v - p v := by
  obtain ⟨s₀, hs₀⟩ := δ.rangeRestrict.exists_rightInverse_of_surjective δ.range_rangeRestrict
  have hs₀v (b : LinearMap.range δ) : δ (s₀ b) = b := by
    exact congrArg Subtype.val (LinearMap.congr_fun hs₀ b)
  let s : LinearMap.range δ →ₗ[K] V := (LinearMap.id - p).comp s₀
  have hs (b : LinearMap.range δ) : δ (s b) = b := by
    change δ (s₀ b-p (s₀ b)) = b
    rw [map_sub, hpZ, sub_zero, hs₀v]
  have hps (b : LinearMap.range δ) : p (s b)=0 := by
    change p (s₀ b-p (s₀ b))=0
    rw [map_sub, hpp, sub_self]
  let z : V →ₗ[K] V := LinearMap.id - p - s.comp δ.rangeRestrict
  have hz (v : V) : z v = v-p v-s (δ.rangeRestrict v) := rfl
  have hzB (v : V) : z v∈LinearMap.range δ := by
    have hd : δ (z v)=0 := by
      rw [hz, map_sub, map_sub, hpZ, hs]
      change δ v-0-δ v=0
      abel
    have hp : p (z v)=0 := by
      rw [hz, map_sub, map_sub, hpp, hps]; abel
    simpa only [hp, sub_zero] using hpmod (z v) hd
  let zB : V →ₗ[K] LinearMap.range δ := z.codRestrict _ hzB
  refine ⟨s.comp zB, ?_⟩
  intro v
  change δ (s (zB v)) + s (zB (δ v)) = v-p v
  rw [hs]
  have hzd : zB (δ v)=δ.rangeRestrict v := by
    apply Subtype.ext
    change z (δ v)=δ v
    rw [hz, hpB]
    have he : δ.rangeRestrict (δ v)=0 := by
      apply Subtype.ext
      exact hδ v
    rw [he, map_zero, sub_zero, sub_zero]
  rw [hzd]
  change z v+s (δ.rangeRestrict v)=v-p v
  rw [hz, sub_add_cancel]

 
theorem exists_odd_contraction [Invertible (2 : K)] (δ p g : V →ₗ[K] V)
    (hg : ∀ v, g (g v)=v)
    (hdg : ∀ v, δ (g v) = -g (δ v))
    (hpg : ∀ v, p (g v) = g (p v))
    (hhom : ∃ h : V →ₗ[K] V, ∀ v, δ (h v)+h (δ v)=v-p v) :
    ∃ h : V →ₗ[K] V,
      (∀ v, δ (h v)+h (δ v)=v-p v) ∧ (∀ v, h (g v) = -g (h v)) := by
  obtain ⟨h, hh⟩ := hhom
  let c : K := (2 : K)⁻¹
  have hc : c+c=1 := by
    dsimp [c]
    rw [← mul_two, inv_mul_cancel₀ (isUnit_of_invertible (2 : K)).ne_zero]
  let q : V →ₗ[K] V := c • (h-g.comp (h.comp g))
  have hq (v : V) : q v=c • (h v-g (h (g v))) := rfl
  have hgd (v : V) : g (δ v) = -δ (g v) := by rw [hdg, neg_neg]
  refine ⟨q, ?_, ?_⟩
  · intro v
    rw [hq, hq]
    simp only [map_smul, map_sub]
    rw [hdg, hgd v]
    simp only [map_neg, sub_neg_eq_add]
    calc
      c • (δ (h v) + g (δ (h (g v)))) + c • (h (δ v) + g (h (δ (g v)))) =
          c • ((δ (h v)+h (δ v)) + g (δ (h (g v))+h (δ (g v)))) := by
        simp only [map_add, smul_add]; abel
      _ = c • ((v-p v)+g (g v-p (g v))) := by rw [hh, hh]
      _ = (c+c) • (v-p v) := by rw [map_sub, hpg, hg, hg, smul_add, add_smul]
      _ = v-p v := by rw [hc, one_smul]
  · intro v
    simp only [hq, hg, map_smul, map_sub, smul_sub, neg_sub]

end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

 

structure SuperReduction where
  d : V →ₗ[K] V
  g : V →ₗ[K] V
  p : V →ₗ[K] V
  h : V →ₗ[K] V
  dd : ∀ v, d (d v)=0
  gg : ∀ v, g (g v)=v
  dg : ∀ v, d (g v) = -g (d v)
  dp : ∀ v, d (p v)=0
  pd : ∀ v, p (d v)=0
  pp : ∀ v, p (p v)=p v
  pg : ∀ v, p (g v)=g (p v)
  hom : ∀ v, d (h v)+h (d v)=v-p v
  hg : ∀ v, h (g v) = -g (h v)

variable {K V}
 
theorem exists_superReduction [Invertible (2 : K)] (d g : V →ₗ[K] V)
    (hdd : ∀ v, d (d v)=0) (hgg : ∀ v, g (g v)=v)
    (hdg : ∀ v, d (g v) = -g (d v)) (W : Submodule K V)
    (hgW : ∀ v∈W, g v∈W) :
    ∃ C : SuperReduction K V, C.d=d ∧ C.g=g ∧ ∀ w∈W, C.p w∈W := by
  have hBZ : LinearMap.range d ≤ LinearMap.ker d := by
    rintro _ ⟨v, rfl⟩; exact hdd v
  have hgB : ∀ b∈LinearMap.range d, g b∈LinearMap.range d := by
    rintro _ ⟨v, rfl⟩
    exact ⟨-g v, by rw [map_neg, hdg, neg_neg]⟩
  have hgZ : ∀ z∈LinearMap.ker d, g z∈LinearMap.ker d := by
    intro z hz; change d (g z)=0
    rw [hdg, hz, map_zero, neg_zero]
  obtain ⟨p, hpZ, hpB, hpmod, hpW, hpp, hpg⟩ :=
    exists_even_cohomology_projection (LinearMap.range d) (LinearMap.ker d) W hBZ
      g hgg hgB hgZ hgW
  have hpd (v : V) : p (d v)=0 := hpB _ (LinearMap.mem_range_self d v)
  have hdp (v : V) : d (p v)=0 := hpZ v
  have hppv : ∀ v, p (p v)=p v := LinearMap.congr_fun hpp
  have hpgv : ∀ v, p (g v)=g (p v) := LinearMap.congr_fun hpg
  obtain ⟨h, hhom, hhg⟩ := exists_odd_contraction d p g hgg hdg hpgv
    (exists_contraction d p hdd hdp hpd hpmod hppv)
  exact ⟨⟨d,g,p,h,hdd,hgg,hdg,hdp,hpd,hppv,hpgv,hhom,hhg⟩, rfl, rfl, hpW⟩

variable {W : Type*} [AddCommGroup W] [Module K W]
namespace SuperReduction

def tensorD (C : SuperReduction K V) (E : SuperReduction K W) :
    V ⊗[K] W →ₗ[K] V ⊗[K] W :=
  TensorProduct.map C.d LinearMap.id + TensorProduct.map C.g E.d

def tensorG (C : SuperReduction K V) (E : SuperReduction K W) :
    V ⊗[K] W →ₗ[K] V ⊗[K] W := TensorProduct.map C.g E.g

def tensorP (C : SuperReduction K V) (E : SuperReduction K W) :
    V ⊗[K] W →ₗ[K] V ⊗[K] W := TensorProduct.map C.p E.p

def tensorH (C : SuperReduction K V) (E : SuperReduction K W) :
    V ⊗[K] W →ₗ[K] V ⊗[K] W :=
  TensorProduct.map C.h LinearMap.id + TensorProduct.map (C.p.comp C.g) E.h

@[simp] theorem tensorD_tmul (C : SuperReduction K V) (E : SuperReduction K W) (v : V) (w : W) :
    tensorD C E (v ⊗ₜ[K] w) = C.d v ⊗ₜ[K] w + C.g v ⊗ₜ[K] E.d w := by simp [tensorD]

@[simp] theorem tensorG_tmul (C : SuperReduction K V) (E : SuperReduction K W) (v : V) (w : W) :
    tensorG C E (v ⊗ₜ[K] w) = C.g v ⊗ₜ[K] E.g w := rfl

@[simp] theorem tensorP_tmul (C : SuperReduction K V) (E : SuperReduction K W) (v : V) (w : W) :
    tensorP C E (v ⊗ₜ[K] w) = C.p v ⊗ₜ[K] E.p w := rfl

@[simp] theorem tensorH_tmul (C : SuperReduction K V) (E : SuperReduction K W) (v : V) (w : W) :
    tensorH C E (v ⊗ₜ[K] w) = C.h v ⊗ₜ[K] w + C.p (C.g v) ⊗ₜ[K] E.h w := by simp [tensorH]

 
theorem tensor_hom (C : SuperReduction K V) (E : SuperReduction K W) (ω : V ⊗[K] W) :
    tensorD C E (tensorH C E ω) + tensorH C E (tensorD C E ω) = ω - tensorP C E ω := by
  induction ω using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add]; rw [add_add_add_comm, ha, hb, add_sub_add_comm]
  | tmul v w =>
    simp only [tensorH_tmul, tensorD_tmul, tensorP_tmul, map_add, C.pg, C.pd,
      C.gg, C.hg, C.dg, C.dp, map_zero, neg_zero, TensorProduct.zero_tmul, zero_add, TensorProduct.neg_tmul]
    calc
      _ = (C.d (C.h v)+C.h (C.d v)) ⊗ₜ[K] w +
          C.p v ⊗ₜ[K] (E.d (E.h w)+E.h (E.d w)) := by
        simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
      _ = _ := by rw [C.hom, E.hom]; simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]

 
def tensor (C : SuperReduction K V) (E : SuperReduction K W) : SuperReduction K (V ⊗[K] W) where
  d := tensorD C E
  g := tensorG C E
  p := tensorP C E
  h := tensorH C E
  dd ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.dd, E.dd, C.dg, TensorProduct.neg_tmul]
  gg ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.gg, E.gg]
  dg ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]; abel
    | tmul v w => simp [C.dg, E.dg, C.gg, TensorProduct.neg_tmul, TensorProduct.tmul_neg]; abel
  dp ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.dp, E.dp]
  pd ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.pd, E.pd]
  pp ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.pp, E.pp]
  pg ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul v w => simp [C.pg, E.pg]
  hom := tensor_hom C E
  hg ω := by
    induction ω using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]; abel
    | tmul v w => simp [C.hg, E.hg, C.pg, C.gg, TensorProduct.neg_tmul, TensorProduct.tmul_neg]; abel

 

theorem tensor_cycle_mod_projection (C : SuperReduction K V) (E : SuperReduction K W)
    (ω : V ⊗[K] W) (hω : tensorD C E ω=0) :
    ω-tensorP C E ω ∈ LinearMap.range (tensorD C E) := by
  refine ⟨tensorH C E ω, ?_⟩
  have h := tensor_hom C E ω
  simpa only [hω, map_zero, add_zero] using h

end SuperReduction
end
end PD4Tensor

namespace PD4Tensor
noncomputable section
open scoped TensorProduct
variable {K ι : Type*} [Field K] [Fintype ι] [LinearOrder ι]
variable {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
namespace SuperReduction
variable (C : ∀ i, SuperReduction K (E i))

def dcoord (i j : ι) : E j →ₗ[K] E j :=
  if j < i then (C j).g else if j = i then (C j).d else LinearMap.id

def hcoord (i j : ι) : E j →ₗ[K] E j :=
  if j < i then (C j).g else if j = i then (C j).h else (C j).p

def finiteD : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i) :=
  ∑ i, PiTensorProduct.map (dcoord C i)

def finiteH : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i) :=
  ∑ i, PiTensorProduct.map (hcoord C i)

def finiteP : (⨂[K] i, E i) →ₗ[K] (⨂[K] i, E i) :=
  PiTensorProduct.map (fun i => (C i).p)

omit [Fintype ι] in
private theorem coord_dh_lt (i j : ι) (hij : i < j) (v : ∀ i, E i) :
    (fun k => dcoord C i k (hcoord C j k (v k))) =
    Function.update (fun k => hcoord C j k (dcoord C i k (v k))) i
      (-hcoord C j i (dcoord C i i (v i))) := by
  funext k
  by_cases hki : k=i
  · subst k
    simp [dcoord, hcoord, hij, (C i).dg]
  · rw [Function.update_of_ne hki]
    by_cases hkj : k=j
    · subst k; simp [dcoord, hcoord, hij.not_gt, hki]
    · by_cases hkin : k < i
      · simp [dcoord, hcoord, hkin, hkin.trans hij]
      · by_cases hkjn : k < j
        · simp [dcoord, hcoord, hkin, hkjn, hki]
        · simp [dcoord, hcoord, hkin, hkjn, hki, hkj]

omit [Fintype ι] in
private theorem pair_offdiagonal (i j : ι) (hij : i ≠ j) :
    (PiTensorProduct.map (dcoord C i)).comp (PiTensorProduct.map (hcoord C j)) +
    (PiTensorProduct.map (hcoord C j)).comp (PiTensorProduct.map (dcoord C i)) = 0 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply,
    LinearMap.comp_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  rcases hij.lt_or_gt with hlt | hgt
  · rw [coord_dh_lt C i j hlt v, (PiTensorProduct.tprod K).map_update_neg,
      Function.update_eq_self]
    exact neg_add_cancel _
  · have hz₁ : PiTensorProduct.tprod K (fun k => dcoord C i k (hcoord C j k (v k)))=0 := by
      apply (PiTensorProduct.tprod K).map_coord_zero i
      simp [dcoord, hcoord, hgt.not_gt, ne_of_gt hgt, (C i).dp]
    have hz₂ : PiTensorProduct.tprod K (fun k => hcoord C j k (dcoord C i k (v k)))=0 := by
      apply (PiTensorProduct.tprod K).map_coord_zero i
      simp [dcoord, hcoord, hgt.not_gt, ne_of_gt hgt, (C i).pd]
    rw [hz₁, hz₂, zero_add]

omit [Fintype ι] in
private theorem pair_diagonal (i : ι) :
    (PiTensorProduct.map (dcoord C i)).comp (PiTensorProduct.map (hcoord C i)) +
    (PiTensorProduct.map (hcoord C i)).comp (PiTensorProduct.map (dcoord C i)) =
    PiTensorProduct.map (fun j => if j < i then LinearMap.id else
      if j=i then LinearMap.id-(C j).p else (C j).p) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply,
    LinearMap.comp_apply, PiTensorProduct.map_tprod]
  let q : ∀ j, E j := fun j => if j < i then v j else (C j).p (v j)
  have h₁ : (fun j => dcoord C i j (hcoord C i j (v j))) =
      Function.update q i ((C i).d ((C i).h (v i))) := by
    funext j
    by_cases hji : j=i
    · subst j; simp [dcoord,hcoord]
    · by_cases hlt : j < i <;> simp [dcoord,hcoord,q,hji,hlt,(C j).gg]
  have h₂ : (fun j => hcoord C i j (dcoord C i j (v j))) =
      Function.update q i ((C i).h ((C i).d (v i))) := by
    funext j
    by_cases hji : j=i
    · subst j; simp [dcoord,hcoord]
    · by_cases hlt : j < i <;> simp [dcoord,hcoord,q,hji,hlt,(C j).gg]
  rw [h₁,h₂,← (PiTensorProduct.tprod K).map_update_add,(C i).hom]
  congr 1
  funext j
  by_cases hji : j=i
  · subst j; simp
  · by_cases hlt : j < i <;> simp [q,hji,hlt]

 
theorem finite_hom : (finiteD C).comp (finiteH C) + (finiteH C).comp (finiteD C) =
    LinearMap.id-finiteP C := by
  apply LinearMap.ext
  intro v
  simp only [finiteD, finiteH, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  have hdiag : ∑ j, ((∑ i, PiTensorProduct.map (dcoord C j)
      (PiTensorProduct.map (hcoord C i) v)) +
      ∑ i, PiTensorProduct.map (hcoord C i)
      (PiTensorProduct.map (dcoord C j) v)) =
    ∑ j, PiTensorProduct.map (fun k => if k < j then LinearMap.id else
      if k=j then LinearMap.id-(C k).p else (C k).p) v := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib, Finset.sum_eq_single j]
    · exact LinearMap.congr_fun (pair_diagonal C j) v
    · intro i _ hij; exact LinearMap.congr_fun (pair_offdiagonal C j i hij.symm) v
    · simp
  rw [hdiag]
  have ht := (PiTensorProduct.mapMultilinear K E E).map_sub_map_piecewise
    (fun i => (LinearMap.id : E i →ₗ[K] E i)) (fun i => (C i).p) Finset.univ
  simp only [Finset.piecewise_univ, Finset.mem_univ, true_implies] at ht
  change PiTensorProduct.map (fun i => LinearMap.id) - PiTensorProduct.map (fun i => (C i).p) =
    ∑ i, PiTensorProduct.map (fun j => if j < i then LinearMap.id else
      if i=j then LinearMap.id-(C j).p else (C j).p) at ht
  rw [PiTensorProduct.map_id] at ht
  have hs : (∑ i, PiTensorProduct.map (fun j => if j < i then LinearMap.id else
      if i=j then LinearMap.id-(C j).p else (C j).p)) =
    ∑ i, PiTensorProduct.map (fun j => if j < i then LinearMap.id else
      if j=i then LinearMap.id-(C j).p else (C j).p) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext j
    simp only [eq_comm]
  rw [hs] at ht
  simpa only [finiteP, LinearMap.sum_apply] using LinearMap.congr_fun ht.symm v

 
theorem finite_cycle_mod_projection (v : ⨂[K] i, E i) (hv : finiteD C v=0) :
    v - finiteP C v ∈ LinearMap.range (finiteD C) := by
  refine ⟨finiteH C v, ?_⟩
  have h := LinearMap.congr_fun (finite_hom C) v
  simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,
    LinearMap.id_apply,hv,map_zero,add_zero] using h

end SuperReduction
end
end PD4Tensor
end

end OAI
