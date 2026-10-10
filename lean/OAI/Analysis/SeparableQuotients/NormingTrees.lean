import OAI.Analysis.SeparableQuotients.MarkedEstimates

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

lemma TypeI.value_ne_zero {f : Family} (e : TypeI f) : e.value ≠ 0 := by
  let h : Fin e.length := ⟨0, e.length_pos⟩
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (e.child_nonzero h)
  have hca := Finsupp.mem_support_iff.mp ha
  have hsum : (∑ i, e.child i) a = e.child h a := by
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single h]
    · intro i _ hih
      by_contra hi
      exact hih (successive_coefficient_unique e.child e.successive hi hca)
    · simp
  intro hz
  have hza := congrArg (fun x : Array => x a) hz
  have hm : (f.m e.weight : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f.m_pos _).ne'
  exact (mul_ne_zero (inv_ne_zero hm) hca) (by
    simpa only [TypeI.value, Finsupp.smul_apply, hsum, smul_eq_mul,
      one_div, Finsupp.zero_apply] using hza)

noncomputable def TypeI.singletonMetadata {f : Family} (e : TypeI f) : ℕ :=
  max e.weight (1 + (e.value.support.product e.value.support).sup (fun p => rho p.1 p.2))

noncomputable def TypeI.singletonRaw {f : Family} (e : TypeI f) : RawPath where
  piece := fun _ => e.value
  weight := fun _ => e.weight
  metadata := fun _ => e.singletonMetadata
  nonzero := fun _ => e.value_ne_zero

lemma TypeI.singletonRaw_valid {f : Family} (e : TypeI f) : PrefixValid e.singletonRaw 1 where
  successive := fun i j hij hj => by omega
  metadata_strict := fun i j hij hj => by omega
  metadata_pos := fun _ _ => by
    exact (by omega : 1 ≤ 1 + (e.value.support.product e.value.support).sup (fun p => rho p.1 p.2)).trans (le_max_right _ _)
  weight_pos := fun _ _ => e.weight_pos
  weight_le_metadata := fun _ _ => le_max_left _ _
  rho_bound := by
    intro n hn a b ha hb _
    have hn0 : n = 0 := by omega
    subst n
    have ha' : a ∈ e.value.support := by simpa [RawPath.support,singletonRaw] using ha
    have hb' : b ∈ e.value.support := by simpa [RawPath.support,singletonRaw] using hb
    exact (Finset.le_sup (s := e.value.support.product e.value.support) (b := (a,b))
      (f := fun p : Γ × Γ => rho p.1 p.2) (Finset.mem_product.mpr ⟨ha',hb'⟩)).trans
      ((Nat.le_add_left _ _).trans (le_max_right _ _))
  rule := fun n hn => by omega

noncomputable def TypeI.singletonPath {f : Family} (e : TypeI f) : FinitePath f where
  raw := e.singletonRaw
  length := 1
  length_pos := le_rfl
  valid := e.singletonRaw_valid
  piece := fun _ => e
  value_eq := fun _ => rfl
  weight_eq := fun _ => rfl
  mixed_successive := fun _i _j hij => (not_lt_of_ge (le_of_eq (Subsingleton.elim _ _)) hij).elim

@[simp] lemma TypeI.singletonPath_value {f : Family} (e : TypeI f) : e.singletonPath.value = e.value := by
  change (∑ _ : Fin 1, e.value) = e.value
  simp

noncomputable def TypeI.toTypeII {f : Family} (e : TypeI f) : TypeII f := e.singletonPath.oneTerm Crop.all

@[simp] lemma TypeI.toTypeII_value {f : Family} (e : TypeI f) : e.toTypeII.value = e.value := by
  simp [toTypeII]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def TypeI.childRange {f : Family} (e : TypeI f) (h : Fin e.length) : Set Γ :=
  ordinalHull (e.child h).support (Finsupp.support_nonempty_iff.mpr (e.child_nonzero h))

lemma TypeI.childRange_connected {f : Family} (e : TypeI f) (h : Fin e.length) :
    Set.OrdConnected (TypeI.childRange e h) := ordinalHull_connected _ _

lemma TypeI.mem_childRange {f : Family} (e : TypeI f) (h : Fin e.length) {a : Γ}
    (ha : a ∈ (e.child h).support) : a ∈ TypeI.childRange e h := mem_ordinalHull _ ha

lemma TypeI.childRange_successive {f : Family} (e : TypeI f) (h k : Fin e.length) (hhk : h < k) :
    ∀ a ∈ TypeI.childRange e h, ∀ b ∈ TypeI.childRange e k, a < b :=
  ordinalHull_successive _ _ (fun a ha b hb => (e.successive h k hhk a ha b hb).1)

noncomputable def TypeI.hitChildren {f : Family} (e : TypeI f) (x : Γ →₀ ℝ) : Finset (Fin e.length) :=
  Finset.univ.filter (fun h => ∃ a ∈ x.support, a ∈ TypeI.childRange e h)

lemma TypeI.cropped_child_zero {f : Family} (e : TypeI f) (A : Crop) (x : Γ →₀ ℝ)
    (h : Fin e.length) (hh : h ∉ TypeI.hitChildren e x) :
    norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h)) = 0 := by
  rw [norming.evaluateArray_eq]
  apply Finset.sum_eq_zero
  intro a ha
  have haR := TypeI.mem_childRange e h (restrict_support_subset _ _ ha)
  have hxa : x a = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hx
    exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, hx, haR⟩)
  simp only [norming.coordinate_includeFinite,hxa,mul_zero]

lemma TypeI.cropped_child_bound {f : Family} (e : TypeI f) (A : Crop)
    (he : ∀ h, e.child h ∈ f.norming) (x : E) (h : Fin e.length) :
    |norming.evaluateArray x (restrict (A.set f) (e.child h))| ≤
      ‖intervalProjection (TypeI.childRange e h) (TypeI.childRange_connected e h) x‖ :=
  abs_eval_supported_interval _ (f.norming_subset_full (family_norming_crop f A _ (he h)))
    _ _ (fun _ ha => TypeI.mem_childRange e h (restrict_support_subset _ _ ha)) x

lemma TypeI.cropped_child_sum_bound {f : Family} (e : TypeI f) (A : Crop)
    (he : ∀ h, e.child h ∈ f.norming) (x : Γ →₀ ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hx : PartitionBound (norming.includeFinite x) N C f.r)
    (hL : e.length ≤ N) :
    ∑ h, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))| ≤
      C * ((TypeI.hitChildren e x).card : ℝ)^(1/f.r) := by
  let S := TypeI.hitChildren e x
  have heq : (∑ h, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))|) =
      ∑ h ∈ S, |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) (e.child h))| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro h _ hh
    simp only [TypeI.cropped_child_zero e A x h hh,abs_zero]
  rw [heq]
  by_cases hS : S.Nonempty
  · let idx := S.orderEmbOfFin rfl
    have hN : S.card ≤ N := (Finset.card_le_univ S).trans (by simpa only [Fintype.card_fin] using hL)
    have hp := hx S.card (by exact hS.card_pos) hN
      (fun i => TypeI.childRange e (idx i)) (fun i => TypeI.childRange_connected e (idx i))
      (fun i j hij => TypeI.childRange_successive e _ _ (idx.strictMono hij))
    calc
      _ ≤ ∑ h ∈ S, ‖intervalProjection (TypeI.childRange e h) (TypeI.childRange_connected e h) (norming.includeFinite x)‖ :=
        Finset.sum_le_sum (fun h _ => TypeI.cropped_child_bound e A he _ h)
      _ = ∑ i : Fin S.card, ‖intervalProjection (TypeI.childRange e (idx i)) (TypeI.childRange_connected e (idx i)) (norming.includeFinite x)‖ := by
        conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl]
        rw [Finset.sum_map]
        rfl
      _ ≤ _ := hp
  · have hSE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hSE,Finset.sum_empty]
    exact mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma TypeI.hitChildren_noncrossing {f : Family} (e : TypeI f) (z : BlockSequence f)
    (i j : ℕ) (hij : i < j) (h k : Fin e.length)
    (hh : h ∈ TypeI.hitChildren e (z.vector i)) (hk : k ∈ TypeI.hitChildren e (z.vector j)) : h ≤ k := by
  apply le_of_not_gt
  intro hkh
  obtain ⟨a, ha, haR⟩ := (Finset.mem_filter.mp hh).2
  obtain ⟨b, hb, hbR⟩ := (Finset.mem_filter.mp hk).2
  have hab := (z.successive i j hij a ha b hb).1
  have hba := TypeI.childRange_successive e k h hkh b hbR a haR
  exact (lt_asymm hab hba)

lemma TypeI.boundary_incidence {f : Family} (e : TypeI f) (z : BlockSequence f) (s : Finset ℕ) :
    ∑ i ∈ s.filter (fun i => 2 ≤ (TypeI.hitChildren e (z.vector i)).card),
      (TypeI.hitChildren e (z.vector i)).card ≤ 2 * e.length := by
  have hh := IntervalIncidence.noncrossing_boundary_incidence s (Finset.univ : Finset (Fin e.length))
      (fun i h => h ∈ TypeI.hitChildren e (z.vector i))
      (fun i _ j _ hij h _ k _ hi hk => TypeI.hitChildren_noncrossing e z i j hij h k hi hk)
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.card_univ,Fintype.card_fin] using hh

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u v
variable {ι : Type u} [Fintype ι] {κ : Type v}

lemma vec_sum (p : ℝ≥0∞) (s : Finset κ) (v : κ → ι → ℝ) :
    vec p (fun i => ∑ k ∈ s, v k i) = ∑ k ∈ s, vec p (v k) := by
  apply lp.ext
  funext i
  simp only [vec_apply,lp.coeFn_sum,Finset.sum_apply]

lemma norm_sum_disjoint_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (s : Finset κ) (v : κ → ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hd : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → ∀ i, v k i = 0 ∨ v l i = 0)
    (hb : ∀ k ∈ s, ‖vec p (v k)‖ ≤ K) :
    ‖vec p (fun i => ∑ k ∈ s, v k i)‖ ≤ K * (s.card : ℝ)^(1/p.toReal) := by
  rw [vec_sum]
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp).mp
  rw [LpFinite.norm_sum_rpow hp s (fun k => vec p (v k)) hd,
    Real.mul_rpow hK (by positivity), ← Real.rpow_mul (Nat.cast_nonneg _),
    one_div_mul_cancel hp.ne',Real.rpow_one]
  calc
    _ ≤ ∑ _k ∈ s, K^p.toReal := Finset.sum_le_sum (fun k hk =>
      Real.rpow_le_rpow (norm_nonneg _) (hb k hk) hp.le)
    _ = _ := by simp [mul_comm]

lemma norm_degree_le {p : ℝ≥0∞} (hp : 0 < p.toReal) (d : ι → ℝ) (A C : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hd : ∀ i, 0 ≤ d i) (hs : ∑ i, d i ≤ C)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ A*(d i)^(1/p.toReal)) :
    ‖vec p v‖ ≤ A*C^(1/p.toReal) := by
  apply norm_le hp _ _ (by positivity)
  calc
    _ ≤ ∑ i, (A*(d i)^(1/p.toReal))^p.toReal :=
      Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (abs_nonneg _) (hv i) hp.le)
    _ = A^p.toReal * ∑ i, d i := by
      simp_rw [Real.mul_rpow hA (Real.rpow_nonneg (hd _) _), ← Real.rpow_mul (hd _),
        one_div_mul_cancel hp.ne',Real.rpow_one]
      rw [Finset.mul_sum]
    _ ≤ A^p.toReal*C := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hA _)
    _ = _ := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hC _), ← Real.rpow_mul hC,
        one_div_mul_cancel hp.ne',Real.rpow_one]

lemma norm_le_sum_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0)
    (s : Finset κ) (v : κ → ι → ℝ) (w : ι → ℝ)
    (hw : ∀ i, |w i| ≤ ∑ k ∈ s, |v k i|) :
    ‖vec p w‖ ≤ ∑ k ∈ s, ‖vec p (v k)‖ := by
  have he (k : κ) : ‖vec p (fun i => |v k i|)‖ = ‖vec p (v k)‖ := by
    apply le_antisymm <;> apply lp.norm_mono hp <;> intro i <;> simp [Real.norm_eq_abs]
  calc
    _ ≤ ‖vec p (fun i => ∑ k ∈ s, |v k i|)‖ := by
      apply lp.norm_mono hp
      intro i
      simpa only [vec_apply,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg (v k i)))] using hw i
    _ = ‖∑ k ∈ s, vec p (fun i => |v k i|)‖ := congrArg norm (vec_sum p s _)
    _ ≤ ∑ k ∈ s, ‖vec p (fun i => |v k i|)‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun k _ => he k)

lemma sum_abs_le_holder {p : ℝ≥0∞} (hp : 1 < p.toReal) (v : ι → ℝ) :
    ∑ i, |v i| ≤ (Fintype.card ι : ℝ)^(1-1/p.toReal) * ‖vec p v‖ := by
  have hcon := Real.HolderConjugate.conjExponent hp
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ (f := fun i => |v i|)
    (g := fun _ => (1 : ℝ)) hcon (fun i _ => abs_nonneg _) (fun _ _ => zero_le_one)
  have hroot : (∑ i, |v i|^p.toReal)^(1/p.toReal) = ‖vec p v‖ := by
    rw [← norm_rpow (zero_lt_one.trans hp), ← Real.rpow_mul (lp.norm_nonneg' _),
      mul_one_div_cancel (zero_lt_one.trans hp).ne',Real.rpow_one]
  have hq : 1/Real.conjExponent p.toReal = 1-1/p.toReal := by
    dsimp [Real.conjExponent]
    field_simp
  simpa only [mul_one,Real.one_rpow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hroot,hq,mul_comm] using hh

end SeparableQuotient.FiniteVectors

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

abbrev TypeII.Group {f : Family} (e : TypeII f) := Σ b : Fin e.length, Fin (e.path b).length

noncomputable def TypeII.groupValue {f : Family} (e : TypeII f) (g : TypeII.Group e) : Array :=
  restrict ((e.crop g.1).set f) (((e.path g.1).piece g.2).value)

def TypeII.groupWeight {f : Family} (e : TypeII f) (g : TypeII.Group e) : ℕ :=
  ((e.path g.1).piece g.2).weight

noncomputable def TypeII.activeGroups {f : Family} (e : TypeII f) : Finset (TypeII.Group e) :=
  Finset.univ.filter (fun g => TypeII.groupValue e g ≠ 0)

lemma TypeII.groupWeight_active {f : Family} (e : TypeII f) {g : TypeII.Group e}
    (hg : g ∈ TypeII.activeGroups e) : TypeII.groupWeight e g ∈ (e.path g.1).active (e.crop g.1) := by
  apply Finset.mem_image.mpr
  refine ⟨g.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · simpa only [TypeII.groupValue,(e.path g.1).value_eq g.2] using (Finset.mem_filter.mp hg).2
  · exact ((e.path g.1).weight_eq g.2).symm

lemma TypeII.groupWeight_injOn {f : Family} (e : TypeII f) :
    Set.InjOn (TypeII.groupWeight e) (TypeII.activeGroups e) := by
  intro g hg h hh hw
  obtain ⟨b,i⟩ := g
  obtain ⟨c,j⟩ := h
  have hbc : b = c := by
    by_contra hbc
    exact Finset.disjoint_left.mp (e.disjoint_active hbc)
      (TypeII.groupWeight_active e hg) (hw.symm ▸ TypeII.groupWeight_active e hh)
  subst c
  have hij : i = j := by
    apply (e.path b).valid.weight_strict.injective
    exact ((e.path b).weight_eq i).symm.trans (hw.trans ((e.path b).weight_eq j))
  subst j
  rfl

lemma TypeII.value_group_sum {f : Family} (e : TypeII f) :
    e.value = ∑ g ∈ TypeII.activeGroups e, e.coefficient g.1 • TypeII.groupValue e g := by
  have heq : e.value = ∑ g : TypeII.Group e, e.coefficient g.1 • TypeII.groupValue e g := by
    rw [Fintype.sum_sigma]
    change (∑ b, e.coefficient b • restrict ((e.crop b).set f) (e.path b).value) = _
    apply Finset.sum_congr rfl
    intro b _
    simp only [FinitePath.value,restrict_sum,Finset.smul_sum,TypeII.groupValue,(e.path b).value_eq]
  rw [heq]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro g _ hg
  have hz : TypeII.groupValue e g = 0 := by simpa only [TypeII.activeGroups,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hg
  simp only [hz,smul_zero]

lemma TypeII.eval_group_sum {f : Family} (e : TypeII f) (x : E) :
    norming.evaluateArray x e.value = ∑ g ∈ TypeII.activeGroups e,
      (e.coefficient g.1 : ℝ) * norming.evaluateArray x (TypeII.groupValue e g) := by
  rw [TypeII.value_group_sum]
  simp only [map_sum,map_smul,Rat.smul_def]

lemma typeI_cropped_eval_le_l1 {f : Family} (e : TypeI f) (A : Crop)
    (hm : ∀ j, e.child j ∈ f.norming) (x : Γ →₀ ℝ) :
    |norming.evaluateArray (norming.includeFinite x) (restrict (A.set f) e.value)| ≤
      vectorL1 x * (1 / (f.m e.weight : ℝ)) := by
  rw [evaluateArray_finite]
  calc
    _ ≤ ∑ a ∈ x.support, |((restrict (A.set f) e.value) a : ℝ) * x a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ x.support, (1 / (f.m e.weight : ℝ)) * |x a| := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      by_cases ha : a ∈ A.set f
      · simpa only [restrict_apply,ite_eq_left ha] using e.coefficient_bound
          (fun j b => full_coefficient_bound _ (f.norming_subset_full (hm j)) b) a
      · simp only [restrict_apply,ite_eq_right ha,Rat.cast_zero,abs_zero]
        positivity
    _ = _ := by rw [← Finset.mul_sum]; dsimp [vectorL1]; ring

lemma TypeII.high_weight_bound {f : Family} (e : TypeII f)
    (hm : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) (x : Γ →₀ ℝ) (T : ℕ) :
    ∑ g ∈ (TypeII.activeGroups e).filter (fun g => T < TypeII.groupWeight e g),
      |(e.coefficient g.1 : ℝ)| * |norming.evaluateArray (norming.includeFinite x) (TypeII.groupValue e g)| ≤
      vectorL1 x * tail (fun j => 1/(f.m j : ℝ)) (T+1) := by
  let S := (TypeII.activeGroups e).filter (fun g => T < TypeII.groupWeight e g)
  have hsum : ∑ g ∈ S, 1/(f.m (TypeII.groupWeight e g) : ℝ) ≤ tail (fun j => 1/(f.m j : ℝ)) (T+1) :=
    sum_le_tail _ f.m_inv_summable (fun _ => by positivity) S (TypeII.groupWeight e)
      ((TypeII.groupWeight_injOn e).mono (Finset.filter_subset _ _)) (T+1)
      (fun g hg => by have h := (Finset.mem_filter.mp hg).2; omega)
  calc
    _ ≤ ∑ g ∈ S, vectorL1 x * (1/(f.m (TypeII.groupWeight e g) : ℝ)) := by
      apply Finset.sum_le_sum
      intro g _
      apply le_trans (mul_le_mul_of_nonneg_right (e.coefficient_le_one g.1) (abs_nonneg _))
      simpa only [one_mul,TypeII.groupValue,TypeII.groupWeight] using
        typeI_cropped_eval_le_l1 ((e.path g.1).piece g.2) (e.crop g.1) (hm g.1 g.2) x
    _ = vectorL1 x * ∑ g ∈ S, 1/(f.m (TypeII.groupWeight e g) : ℝ) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (vectorL1_nonneg x)

end SeparableQuotient.ActualSpace

end

end OAI
