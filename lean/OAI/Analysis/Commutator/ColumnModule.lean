import Mathlib
import OAI.Analysis.Commutator.LittleGrothendieck

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace CStarAlgebra

open Filter Set

namespace Kadison.ColumnModule

variable {A E : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma regularized_factor (a : A) {ε : ℝ} (hε : 0<ε) :
    ∃ b c : A, ‖b‖≤ 1 ∧ IsSelfAdjoint c ∧
      c*c=star a*a+ε • (1:A) ∧ a=b*c := by
  let d := star a*a+ε • (1:A)
  have hd : IsStrictlyPositive d := by
    simpa only [d,add_comm] using
      (IsStrictlyPositive.smul hε (isStrictlyPositive_one (A:=A))).add_nonneg
        (star_mul_self_nonneg a)
  let c := CFC.sqrt d
  have hc : IsSelfAdjoint c := (CFC.sqrt_nonneg d).isSelfAdjoint
  have hcunit : IsUnit c := CFC.isUnit_sqrt_iff_isStrictlyPositive.mpr hd
  let v : Aˣ := hcunit.unit
  have hv : (v:A)=c := hcunit.unit_spec
  have hvs : star (v:A)=(v:A) := by rw [hv]; exact hc.star_eq
  have hivi : star ((v⁻¹:Aˣ):A)=((v⁻¹:Aˣ):A) := by
    have ht : star v=v := Units.ext hvs
    change ((star (v⁻¹):Aˣ):A)=((v⁻¹:Aˣ):A)
    rw [star_inv,ht]
  let b := a*((v⁻¹:Aˣ):A)
  have hcc : c*c=d := CFC.sqrt_mul_sqrt_self d hd.nonneg
  have hs : star b*b≤ 1 := by
    have hle : star a*a ≤ d := le_add_of_nonneg_right (smul_nonneg hε.le zero_le_one)
    have hh := star_left_conjugate_le_conjugate hle (((v⁻¹:Aˣ):A))
    have he : star ((v⁻¹:Aˣ):A)*d*((v⁻¹:Aˣ):A)=1 := by
      rw [hivi,←hcc,←hv]
      simp only [←mul_assoc,Units.inv_mul,one_mul,Units.mul_inv]
    rw [he] at hh
    simpa only [b,star_mul,mul_assoc] using hh
  have hn : ‖b‖≤ 1 := by
    have hh := (CStarAlgebra.norm_le_one_iff_of_nonneg (star b*b)
      (star_mul_self_nonneg b)).mpr hs
    rw [CStarRing.norm_star_mul_self] at hh
    nlinarith [norm_nonneg b]
  refine ⟨b,c,hn,hc,hcc,?_⟩
  simp only [b,←hv,mul_assoc,Units.inv_mul,mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjoint_square_max (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : A) (ha : IsSelfAdjoint a) :
    ‖T (a*(u:A))‖^2 ≤ (inner ℂ (T (u:A)) (T ((a*a)*(u:A)))).re := by
  let S : A →L[ℂ] E := T.comp ((ContinuousLinearMap.mul ℂ A).flip (u:A))
  have hS : ∀ v : unitary A, ‖S (v:A)‖≤‖S (1:A)‖ := by
    intro v
    simpa only [S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.mul_apply',one_mul,Submonoid.coe_mul] using hu (v*u)
  simpa only [S,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply',OneMemClass.coe_one,one_mul] using
      LittleGrothendieck.selfAdjoint_square_at_unitary_max S 1 hS a ha

def maxFunctional (T : A →L[ℂ] E) (u : unitary A) : A →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ (T (u:A))).comp
    (T.comp ((ContinuousLinearMap.mul ℂ A).flip (u:A)))).restrictScalars ℝ)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma maxFunctional_apply (T : A →L[ℂ] E) (u : unitary A) (a : A) :
    maxFunctional T u a=(inner ℂ (T (u:A)) (T (a*(u:A)))).re := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma maxFunctional_one (T : A →L[ℂ] E) (u : unitary A) :
    maxFunctional T u 1=‖T (u:A)‖^2 := by
  simp only [maxFunctional_apply,one_mul]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) _

lemma maxFunctional_nonneg (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) {a : A} (ha : 0≤a) :
    0≤ maxFunctional T u a := by
  have h := selfAdjoint_square_max T u hu (CFC.sqrt a)
    (CFC.sqrt_nonneg a).isSelfAdjoint
  rw [CFC.sqrt_mul_sqrt_self a ha] at h
  exact (sq_nonneg _).trans h

lemma maxFunctional_mono (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) :
    Monotone (maxFunctional T u) := by
  intro a b hab
  have h := maxFunctional_nonneg T u hu (sub_nonneg.mpr hab)
  rwa [map_sub,sub_nonneg] at h

lemma maxFunctional_bound (T : A →L[ℂ] E) (u : unitary A)
    (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖) {a : A}
    (ha : IsSelfAdjoint a) : maxFunctional T u a≤‖a‖*‖T (u:A)‖^2 := by
  have h := maxFunctional_mono T u hu ha.le_algebraMap_norm_self
  simpa only [Algebra.algebraMap_eq_smul_one,map_smul,maxFunctional_one,smul_eq_mul] using h

lemma module_square_max (T : A →L[ℂ] E) {M : ℝ} (hM : 0≤ M)
    (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (u : unitary A) (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : A) : ‖T (a*(u:A))‖^2≤ M^2*maxFunctional T u (star a*a) := by
  have heps (ε : ℝ) (hε : 0<ε) :
      ‖T (a*(u:A))‖^2≤ M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1) := by
    obtain ⟨b,c,hb,hc,hcc,hbc⟩ := regularized_factor a hε
    have hn : ‖T (a*(u:A))‖≤ M*‖T (c*(u:A))‖ := by
      rw [hbc,mul_assoc]
      exact (hmod b (c*(u:A))).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb hM) (norm_nonneg (T (c*(u:A)))))
    have hs := selfAdjoint_square_max T u hu c hc
    change ‖T (c*(u:A))‖^2≤ maxFunctional T u (c*c) at hs
    rw [hcc,map_add,map_smul,smul_eq_mul] at hs
    calc
      _ ≤ (M*‖T (c*(u:A))‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = M^2*‖T (c*(u:A))‖^2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg M)
  have hlim : Tendsto
      (fun ε : ℝ => M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1))
      (𝓝[>] 0) (𝓝 (M^2*maxFunctional T u (star a*a))) := by
    have h : Continuous (fun ε : ℝ => M^2*(maxFunctional T u (star a*a)+ε*maxFunctional T u 1)) := by
      fun_prop
    simpa only [zero_mul,add_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Filter.eventually_of_mem self_mem_nhdsWithin heps)

theorem sum_sq_at_max {ι : Type*} [Fintype ι]
    (T : A →L[ℂ] E) {M : ℝ} (hM : 0≤ M)
    (hmod : ∀ a b : A, ‖T (a*b)‖≤ M*‖a‖*‖T b‖)
    (u : unitary A) (hu : ∀ v : unitary A, ‖T (v:A)‖≤‖T (u:A)‖)
    (a : ι → A) : ∑ i, ‖T (a i)‖^2≤ M^2*‖T‖^2*‖∑ i,star (a i)*a i‖ := by
  classical
  let b : ι → A := fun i => a i*(star u:A)
  have hb (i : ι) : b i*(u:A)=a i := by
    simp only [b,mul_assoc,Unitary.star_mul_self_of_mem u.property,mul_one]
  have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => module_square_max T hM hmod u hu (b i))
  simp only [hb,←Finset.mul_sum,←map_sum] at hs
  have hpos : 0≤∑ i,star (b i)*b i := Finset.sum_nonneg (fun _ _ => star_mul_self_nonneg _)
  have hn : ‖∑ i,star (b i)*b i‖=‖∑ i,star (a i)*a i‖ := by
    have he : (∑ i,star (b i)*b i)=(u:A)*(∑ i,star (a i)*a i)*(star u:A) := by
      simp only [b,star_mul,star_star,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    rw [he]
    change ‖(u:A)*(∑ i,star (a i)*a i)*(↑(star u):A)‖=_
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  have huT : ‖T (u:A)‖≤‖T‖ := by
    cases subsingleton_or_nontrivial A with
    | inl h => simpa only [Subsingleton.elim (u:A) 0,map_zero,norm_zero] using norm_nonneg T
    | inr h => simpa only [CStarRing.norm_coe_unitary,mul_one] using T.le_opNorm (u:A)
  calc
    _ ≤ M^2*maxFunctional T u (∑ i,star (b i)*b i) := hs
    _ ≤ M^2*(‖∑ i,star (b i)*b i‖*‖T (u:A)‖^2) :=
      mul_le_mul_of_nonneg_left (maxFunctional_bound T u hu hpos.isSelfAdjoint) (sq_nonneg M)
    _ ≤ M^2*(‖∑ i,star (b i)*b i‖*‖T‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) huT 2) (norm_nonneg _)) (sq_nonneg M)
    _ = _ := by rw [hn]; ring

end Kadison.ColumnModule

end

end
end

end OAI
