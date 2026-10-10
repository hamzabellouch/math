import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerToTracial

namespace OAI

noncomputable section


namespace Quasicentral
open Filter Topology
open scoped ComplexOrder NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def resolvent (a : A) : A := cfcₙ (fun x : ℝ≥0 => 1-(1+x)⁻¹) a
lemma resolvent_nonneg (a : A) : 0 ≤ resolvent a := cfcₙ_nonneg_of_predicate
lemma resolvent_norm_lt_one (a : A) : ‖resolvent a‖<1 := norm_cfcₙ_one_sub_one_add_inv_lt_one a
lemma resolvent_le_one (a : A) : resolvent a ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (resolvent_nonneg a)).mp (resolvent_norm_lt_one a).le
lemma resolvent_mono {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    resolvent a ≤ resolvent b := CFC.monotoneOn_one_sub_one_add_inv ha hb hab

lemma conjugate_mono (u : unitary A) {a b : A} (hab : a ≤ b) :
    conjugate u a ≤ conjugate u b := by
  have h := conjugate_nonneg u (sub_nonneg.mpr hab)
  rwa [map_sub, sub_nonneg] at h

lemma conjugate_resolvent (u : unitary A) (a : A) (ha : 0 ≤ a) :
    conjugate u (resolvent a)=resolvent (conjugate u a) := by
  change (Unitary.conjStarAlgAut ℂ A u).toNonUnitalStarAlgHom (resolvent a)=_
  exact (Unitary.conjStarAlgAut ℂ A u).toNonUnitalStarAlgHom.map_cfcₙ
    (fun x : ℝ≥0 => 1-(1+x)⁻¹) a (by fun_prop (disch := intro _ _; positivity)) (by simp)
    (by fun_prop) ha (conjugate_nonneg u ha)

omit [PartialOrder A] [StarOrderedRing A] in
lemma conjugate_star_cancel (u : unitary A) (a : A) :
    conjugate u (conjugate (star u) a)=a := by
  simp only [conjugate_apply,Unitary.coe_star,star_star]
  simp only [← mul_assoc]
  simp [mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma conjugate_one (u : unitary A) : conjugate u (1:A)=1 := by
  simp [conjugate_apply]

lemma selfadjoint_norm_le_of_order_bounds {a : A} (ha : IsSelfAdjoint a)
    {r : ℝ} (hr : 0 ≤ r) (hl : -(r • (1:A)) ≤ a) (hu : a ≤ r • (1:A)) :
    ‖a‖ ≤ r := by
  by_cases hA : Nontrivial A
  · have := hA
    rw [← Algebra.algebraMap_eq_smul_one] at hu
    rw [← Algebra.algebraMap_eq_smul_one,← map_neg] at hl
    have hlu := (le_algebraMap_iff_spectrum_le ha).mp hu
    have hll := (algebraMap_le_iff_le_spectrum ha).mp hl
    rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum a ha with hp | hn
    · exact hlu _ hp
    · exact neg_le_neg_iff.mp (hll _ hn)
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    simpa only [Subsingleton.elim a 0,norm_zero] using hr

def logarithmicAverage (C t : ℝ) (h : A) (N : ℕ) : A :=
  (N:ℝ)⁻¹ • ∑ k ∈ Finset.range N, resolvent ((t*C^k) • h)

lemma logarithmicAverage_nonneg (C t : ℝ) (h : A) (N : ℕ) :
    0 ≤ logarithmicAverage C t h N := by
  exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun k _ => resolvent_nonneg _)

lemma logarithmicAverage_le_one (C t : ℝ) (h : A) {N : ℕ} (hN : 0<N) :
    logarithmicAverage C t h N ≤ 1 := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  calc
    _ ≤ (N:ℝ)⁻¹ • ∑ _k ∈ Finset.range N, (1:A) :=
      smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun k _ => resolvent_le_one _) (inv_nonneg.mpr hn.le)
    _ = 1 := by simp [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,hn.ne']

lemma logarithmicAverage_conjugate_le (C t : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t)
    {h : A} (hh : 0 ≤ h) {N : ℕ} (_hN : 0<N) (u : unitary A)
    (hdom : conjugate u h ≤ C • h) :
    conjugate u (logarithmicAverage C t h N) ≤
      logarithmicAverage C t h N + (N:ℝ)⁻¹ • (1:A) := by
  let f : ℕ → A := fun k => resolvent ((t*C^k) • h)
  have hs (k : ℕ) : conjugate u (f k) ≤ f (k+1) := by
    dsimp only [f]
    have htk : 0 ≤ t*C^k := mul_nonneg ht (pow_nonneg hC k)
    rw [conjugate_resolvent u _ (smul_nonneg htk hh), map_smul]
    apply (resolvent_mono (smul_nonneg htk (conjugate_nonneg u hh))
      (smul_nonneg htk (smul_nonneg hC hh))
      (smul_le_smul_of_nonneg_left hdom htk)).trans_eq
    congr 1
    rw [smul_smul,pow_succ,mul_assoc]
  have he : ∑ k ∈ Finset.range N, f (k+1) =
      (∑ k ∈ Finset.range N, f k) + f N - f 0 := by
    have e := (Finset.sum_range_succ f N).symm.trans (Finset.sum_range_succ' f N)
    exact eq_sub_iff_add_eq.mpr e.symm
  have hsum : ∑ k ∈ Finset.range N, f (k+1) ≤
      (∑ k ∈ Finset.range N, f k)+(1:A) := by
    rw [he]
    exact (sub_le_self _ (resolvent_nonneg _)).trans (add_le_add le_rfl (resolvent_le_one _))
  rw [logarithmicAverage,map_smul,map_sum]
  calc
    _ ≤ (N:ℝ)⁻¹ • ∑ k ∈ Finset.range N, f (k+1) :=
      smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun k _ => hs k)
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ ≤ (N:ℝ)⁻¹ • ((∑ k ∈ Finset.range N, f k)+(1:A)) :=
      smul_le_smul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = _ := by rw [smul_add]

lemma logarithmicAverage_commutator_bound (C t : ℝ) (hC : 0≤C) (ht : 0≤t)
    {h : A} (hh : 0≤h) {N : ℕ} (hN : 0<N) (u : unitary A)
    (hdom : conjugate u h ≤ C • h) (hdomstar : conjugate (star u) h ≤ C • h) :
    ‖(u:A)*logarithmicAverage C t h N-logarithmicAverage C t h N*(u:A)‖ ≤ (N:ℝ)⁻¹ := by
  let e := logarithmicAverage C t h N
  have he : 0≤e := logarithmicAverage_nonneg C t h N
  have hup := logarithmicAverage_conjugate_le C t hC ht hh hN u hdom
  have hlo := conjugate_mono u (logarithmicAverage_conjugate_le C t hC ht hh hN (star u) hdomstar)
  rw [conjugate_star_cancel,map_add,map_smul,conjugate_one] at hlo
  have hb : ‖conjugate u e-e‖ ≤ (N:ℝ)⁻¹ :=
    selfadjoint_norm_le_of_order_bounds ((IsSelfAdjoint.of_nonneg (conjugate_nonneg u he)).sub (.of_nonneg he))
      (inv_nonneg.mpr (Nat.cast_nonneg N)) (by
        apply (le_sub_iff_add_le).mpr
        exact (neg_add_le_iff_le_add).mpr (by simpa [e,add_comm] using hlo))
      (by exact sub_le_iff_le_add.mpr (by simpa [e,add_comm] using hup))
  calc
    _ = ‖(conjugate u e-e)*(u:A)‖ := by
      congr 1
      simp [conjugate_apply,sub_mul,mul_assoc,e]
    _ = ‖conjugate u e-e‖ := (Unitary.mulRight ℝ u).norm_map _
    _ ≤ _ := hb

end Quasicentral


namespace Quasicentral
open Filter Topology CStarAlgebra
open scoped ComplexOrder NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nnreal_cfc_mem (J : NonUnitalStarSubalgebra ℂ A) (hJ : IsClosed (J : Set A))
    (f : ℝ≥0 → ℝ≥0) {a : A} (ha : a ∈ J) (hp : 0 ≤ a) : cfcₙ f a ∈ J := by
  have := hJ
  rw [cfcₙ_nnreal_eq_real f a hp]
  exact cfcₙ_mem _ ha

def inverseResolvent (e : A) : A := cfcₙ (fun x : ℝ≥0 => x*(1-x)⁻¹) e
lemma inverseResolvent_nonneg (e : A) : 0 ≤ inverseResolvent e := cfcₙ_nonneg_of_predicate
lemma resolvent_inverseResolvent {e : A} (he : 0≤e) (hn : ‖e‖<1) :
    resolvent (inverseResolvent e)=e := by
  let f := fun x : ℝ≥0 => 1-(1+x)⁻¹
  let g := fun x : ℝ≥0 => x*(1-x)⁻¹
  have hfc : ContinuousOn f (g '' quasispectrum ℝ≥0 e) := by
    fun_prop (disch := intro _ _; positivity)
  have hgc : ContinuousOn g (quasispectrum ℝ≥0 e) := by
    have hx (x : ℝ≥0) (hx : x ∈ quasispectrum ℝ≥0 e) : 1-x ≠ 0 := by
      apply ne_of_gt
      apply tsub_pos_of_lt
      exact lt_of_le_of_lt (le_nnnorm_of_mem_quasispectrum hx) hn
    fun_prop
  change cfcₙ f (cfcₙ g e)=e
  rw [← cfcₙ_comp f g e hfc (by simp [f]) hgc (by simp [g]) he]
  conv_rhs => rw [← cfcₙ_id ℝ≥0 e]
  apply cfcₙ_congr
  apply Set.InvOn.one_sub_one_add_inv.1.eqOn.mono
  intro x hx
  exact lt_of_le_of_lt (le_nnnorm_of_mem_quasispectrum hx) hn

lemma logarithmicAverage_dominates {C : ℝ} (hC : 1≤C) {h e : A}
    (hh : 0≤h) (he : e ≤ resolvent h) {N : ℕ} (hN : 0<N) :
    e ≤ logarithmicAverage C 1 h N := by
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hk (k : ℕ) : e ≤ resolvent ((1*C^k)•h) := by
    apply he.trans
    apply resolvent_mono hh (smul_nonneg (by positivity) hh)
    simpa only [one_mul,one_smul] using smul_le_smul_of_nonneg_right (one_le_pow₀ hC) hh
  calc
    e = (N:ℝ)⁻¹ • ∑ _k ∈ Finset.range N, e := by
      simp [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,hn.ne']
    _ ≤ _ := smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun k _ => hk k) (inv_nonneg.mpr hn.le)

theorem exists_logarithmic_contraction (J : NonUnitalStarSubalgebra ℂ A)
    (hJ : IsClosed (J : Set A)) (K : Finset (unitary A))
    (hKstar : ∀ u∈K, star u∈K)
    (hJK : ∀ u∈K, ∀ a∈J, conjugate u a∈J)
    {e₀ : A} (he₀J : e₀∈J) (he₀ : 0≤e₀) (he₀n : ‖e₀‖<1)
    {N : ℕ} (hN : 0<N) :
    ∃ e : A, e∈J ∧ 0≤e ∧ e≤1 ∧ e₀≤e ∧
      ∀ u∈K, ‖(u:A)*e-e*(u:A)‖ ≤ (N:ℝ)⁻¹ := by
  let h₀ := inverseResolvent e₀
  have hh₀ : h₀∈J := nnreal_cfc_mem J hJ _ he₀J he₀
  obtain ⟨h,hhJ,hh,hh₀h,hhdom⟩ := exists_invariant_domination K
    (J.toSubmodule.restrictScalars ℝ) hJ hJK h₀ hh₀ (inverseResolvent_nonneg e₀)
  let C := expansionConstant K
  have hC : 1≤C := by dsimp only [C,expansionConstant]; have := Nat.cast_nonneg (α := ℝ) K.card; linarith
  let e := logarithmicAverage C 1 h N
  have heJ : e∈J := by
    apply J.smul_mem
    apply J.sum_mem
    intro k _
    exact nnreal_cfc_mem J hJ _ (J.smul_mem _ hhJ) (smul_nonneg (by positivity) hh)
  refine ⟨e,heJ,logarithmicAverage_nonneg C 1 h N,
    logarithmicAverage_le_one C 1 h hN,?_,?_⟩
  · apply logarithmicAverage_dominates hC hh _ hN
    calc
      e₀ = resolvent h₀ := (resolvent_inverseResolvent he₀ he₀n).symm
      _ ≤ resolvent h := resolvent_mono (inverseResolvent_nonneg e₀) hh hh₀h
  · intro u hu
    exact logarithmicAverage_commutator_bound C 1 (zero_le_one.trans hC) zero_le_one hh hN u
      (hhdom u hu) (hhdom (star u) (hKstar u hu))

end Quasicentral

end

end OAI
