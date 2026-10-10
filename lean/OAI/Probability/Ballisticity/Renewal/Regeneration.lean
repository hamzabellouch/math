import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedCoordinate

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def RegenerationSupport {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | X 0 = 0 ∧ ∀ n, ((renewSuffix ℓ)^[n] X) ∈
    FirstWordEvent ℓ (regenerationWords ℓ X n)}

lemma measurableSet_regenerationSupport {d : ℕ} (ℓ : Vector d) :
    MeasurableSet (RegenerationSupport ℓ) := by
  have hm (n : ℕ) : MeasurableSet {X : Path d | ((renewSuffix ℓ)^[n] X) ∈
      FirstWordEvent ℓ (regenerationWords ℓ X n)} := by
    have he : {X : Path d | ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)} =
        ⋃ w : List (Direction d), {X | regenerationWords ℓ X n = w} ∩
          ((renewSuffix ℓ)^[n]) ⁻¹' FirstWordEvent ℓ w := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨w,hw,h⟩ => hw ▸ h⟩
    rw [he]
    exact MeasurableSet.iUnion fun w =>
      ((measurable_regenerationWord ℓ n) (measurableSet_singleton w)).inter
      ((measurableSet_firstWordEvent ℓ w).preimage ((measurable_renewSuffix ℓ).iterate n))
  unfold RegenerationSupport
  rw [Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
    (MeasurableSet.iInter hm)

lemma conditioned_regenerationSupport {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ RegenerationSupport ℓ := by
  filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν),
    conditioned_all_firstWords ν ℓ htrans] with X h0 hX
  exact ⟨h0,hX⟩

lemma regenerationSupport_noDrop {d : ℕ} (ℓ : Vector d) : RegenerationSupport ℓ ⊆ NoDrop ℓ 0 :=
  fun _ h => (h.2 0).1

lemma template_span_estimates {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) (X : Path d)
    (hX : X ∈ RegenerationSupport ℓ) (ht : X ∈ WordTemplate ℓ c C C0 a K)
    {k j : ℕ} (hk : k < K) (hj : j ≤ (regenerationWords ℓ X k).length) :
    c*k-C0 ≤ dot (realPosition (X (regenerationTimes ℓ X k+j))) ℓ ∧
    dot (realPosition (X (regenerationTimes ℓ X k+j))) ℓ ≤ C*(k+1)+C0 ∧
    ‖latticeVector (X (regenerationTimes ℓ X k+j))‖ ≤ a*(k+1) := by
  obtain ⟨⟨hlo,hhi⟩,hR⟩ := regeneration_span_bounds ℓ X hX.1 hX.2 k j hj
  rw [regeneration_height_sum ℓ X hX.1 hX.2 k] at hlo
  rw [regeneration_height_sum ℓ X hX.1 hX.2 (k+1)] at hhi
  rw [← Finset.sum_range_succ] at hR
  refine ⟨(ht k hk.le).1.trans hlo,?_,?_⟩
  · exact hhi.trans (by simpa only [Nat.cast_add, Nat.cast_one] using (ht (k+1) hk).2.1)
  · exact hR.trans (by simpa only [Nat.cast_add, Nat.cast_one] using (ht (k+1) hk).2.2)

lemma signedCoordinate_nsmul {d : ℕ} (u : Direction d) (x : Lattice d) (n : ℕ) :
    signedCoordinate u (n • x) = n * signedCoordinate u x := by
  induction n with
  | zero => simp [signedCoordinate]
  | succ n ih => rw [succ_nsmul, signedCoordinate_add, ih, Nat.cast_add, Nat.cast_one]; ring

lemma tiltedCoordinate_nsmul {d : ℕ} (ℓ : Vector d) (u : Direction d) (b a : ℝ)
    (x : Lattice d) (n : ℕ) :
    tiltedCoordinate ℓ u b a (n • x) = n * tiltedCoordinate ℓ u b a x := by
  rw [tiltedCoordinate, signedCoordinate_nsmul, dot_realPosition_nsmul, tiltedCoordinate]
  ring

lemma template_tilted_lower {d : ℕ} (ℓ : Vector d) (u e : Direction d)
    (c C C0 a b : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a) (K M : ℕ) (X : Path d)
    (hX : X ∈ RegenerationSupport ℓ) (ht : X ∈ WordTemplate ℓ c C C0 a K)
    {k j : ℕ} (hk : k < K) (hj : j ≤ (regenerationWords ℓ X k).length) :
    a*((b*c-1)*k + (b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1)) - M ≤
      tiltedCoordinate ℓ u b a (M • step e + X (regenerationTimes ℓ X k+j)) := by
  obtain ⟨hlo,_,hR⟩ := template_span_estimates ℓ c C C0 a K X hX ht hk hj
  have hcoord : -a*(k+1) ≤ signedCoordinate u (X (regenerationTimes ℓ X k+j)) :=
    by
      have habs := signedCoordinate_abs_le_norm u (X (regenerationTimes ℓ X k+j))
      have hneg := neg_abs_le (signedCoordinate u (X (regenerationTimes ℓ X k+j)))
      linarith
  have hscript : -(1 : ℝ) ≤ signedCoordinate u (step e) := by
    have hh := signedCoordinate_abs_le_norm u (step e)
    rw [latticeVector_step_norm] at hh
    exact (neg_le_neg hh).trans (neg_abs_le _)
  have hM := mul_le_mul_of_nonneg_left hscript (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  have hh := mul_le_mul_of_nonneg_left hlo (mul_nonneg hb ha)
  rw [tiltedCoordinate_add, tiltedCoordinate_nsmul]
  dsimp only [tiltedCoordinate]
  nlinarith

lemma wordPath_replicate_prefix {d : ℕ} (x : Lattice d) (e : Direction d) (M j : ℕ)
    (hj : j ≤ M) : wordPath x (List.replicate M e) j = x + j • step e := by
  induction M generalizing x j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ M ih =>
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.replicate_succ, wordPath]
      rw [ih (x+step e) j (by omega), succ_nsmul]
      abel

def ForwardTemplate {d : ℕ} (ℓ : Vector d) (e : Direction d) (c C C0 a : ℝ)
    (K M : ℕ) : Set (Path d) :=
  ((fun X : Path d => fun j => X (M+j) - M • step e) ⁻¹'
    (RegenerationSupport ℓ ∩ WordTemplate ℓ c C C0 a K)) ∩
      wordCylinder 0 (List.replicate M e)

lemma measurableSet_forwardTemplate {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) : MeasurableSet (ForwardTemplate ℓ e c C C0 a K M) :=
  (((measurableSet_regenerationSupport ℓ).inter
    (measurableSet_wordTemplate ℓ c C C0 a K)).preimage (by fun_prop)).inter
      (measurableSet_wordCylinder 0 (List.replicate M e))

lemma forwardTemplate_script {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) {X : Path d}
    (hX : X ∈ ForwardTemplate ℓ e c C C0 a K M) {j : ℕ} (hj : j ≤ M) :
    X j = j • step e := by
  have hh := hX.2 j (by simpa only [List.length_replicate] using hj)
  rw [wordPath_replicate_prefix _ _ _ _ hj, zero_add] at hh
  exact hh

lemma forwardTemplate_noDrop {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (c C C0 a : ℝ) (K M : ℕ) (he : 0 ≤ dot (realPosition (step e)) ℓ) :
    ForwardTemplate ℓ e c C C0 a K M ⊆ NoDrop ℓ 0 := by
  intro X hX j
  have hz : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  rw [hz]
  by_cases hj : j ≤ M
  · rw [forwardTemplate_script ℓ e c C C0 a K M hX hj, dot_realPosition_nsmul]
    exact mul_nonneg (Nat.cast_nonneg _) he
  · have hs := regenerationSupport_noDrop ℓ hX.1.1 (j-M)
    change dot (realPosition 0) ℓ ≤ dot (realPosition (X (M+(j-M))-M • step e)) ℓ at hs
    rw [Nat.add_sub_of_le (by omega), dot_realPosition_sub, dot_realPosition_nsmul, hz] at hs
    exact (mul_nonneg (Nat.cast_nonneg M) he).trans (sub_nonneg.mp hs)

lemma forwardTemplate_control {d : ℕ} (ℓ : Vector d) (u e : Direction d)
    (c C C0 a b D H : ℝ) (K M : ℕ)
    (ha : 1 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ dot (realPosition (step e)) ℓ)
    (hbc : 1 ≤ b*c) (hM : 0 ≤ (M : ℝ)*dot (realPosition (step e)) ℓ-C0)
    (hconst : (M : ℝ) ≤ a*(b*((M : ℝ)*dot (realPosition (step e)) ℓ)-b*C0-1))
    (hstep : 0 ≤ tiltedCoordinate ℓ u b a (step e))
    (hD : (M : ℝ)+1 ≤ D) (hDc : 1 ≤ D*c)
    (hH : H < (M : ℝ)*dot (realPosition (step e)) ℓ+c*K-C0)
    {X : Path d} (hX : X ∈ ForwardTemplate ℓ e c C C0 a K M) (n : ℕ) :
    0 ≤ dot (realPosition (X n)) ℓ ∧
    ((0 ≤ tiltedCoordinate ℓ u b a (X n) ∧
      signedCoordinate u (X n) ≤ a*D*(1+dot (realPosition (X n)) ℓ)) ∨
      H < dot (realPosition (X n)) ℓ) := by
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by linarith [Nat.cast_nonneg M (α := ℝ)]
  have hnonneg : 0 ≤ dot (realPosition (X n)) ℓ := by
    simpa [dot, realPosition] using
      forwardTemplate_noDrop ℓ e c C C0 a K M he hX n
  refine ⟨hnonneg,?_⟩
  by_cases hn : n < M
  · left
    rw [forwardTemplate_script ℓ e c C C0 a K M hX hn.le, tiltedCoordinate_nsmul,
      signedCoordinate_nsmul]
    refine ⟨mul_nonneg (Nat.cast_nonneg n) hstep,?_⟩
    have hcoord : signedCoordinate u (step e) ≤ 1 := by
      have hh := signedCoordinate_abs_le_norm u (step e)
      rw [latticeVector_step_norm] at hh
      exact (le_abs_self _).trans hh
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast hn.le
    have hu := mul_le_mul_of_nonneg_left hcoord (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hbase : (M : ℝ) ≤ a*D := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
    have hg := mul_nonneg (mul_nonneg ha0 hD0) hnonneg
    have hx := forwardTemplate_script ℓ e c C C0 a K M hX hn.le
    rw [hx] at hnonneg hg
    nlinarith
  · let Y : Path d := fun j => X (M+j)-M • step e
    have hY : Y ∈ RegenerationSupport ℓ := hX.1.1
    have ht : Y ∈ WordTemplate ℓ c C C0 a K := hX.1.2
    have hx (j : ℕ) : X (M+j) = M • step e + Y j := by dsimp only [Y]; abel
    have hnM : M ≤ n := by omega
    have hnm : M+(n-M) = n := Nat.add_sub_of_le hnM
    by_cases hcut : n-M < regenerationTimes ℓ Y K
    · obtain ⟨k,hk,hk'⟩ := increasing_cuts_cover (regenerationTimes ℓ Y)
        (regenerationTimes_strictMono ℓ Y hY.2) (regenerationTimes_zero ℓ Y) (n-M)
      have hkK : k < K := (regenerationTimes_strictMono ℓ Y hY.2).lt_iff_lt.mp (hk.trans_lt hcut)
      have hj : n-M-regenerationTimes ℓ Y k ≤ (regenerationWords ℓ Y k).length := by
        rw [regenerationTimes_succ] at hk'
        omega
      have heq : regenerationTimes ℓ Y k+(n-M-regenerationTimes ℓ Y k) = n-M :=
        Nat.add_sub_of_le hk
      have hlow := template_tilted_lower ℓ u e c C C0 a b hb ha0 K M Y hY ht hkK hj
      rw [heq] at hlow
      obtain ⟨hh,_,hr⟩ := template_span_estimates ℓ c C C0 a K Y hY ht hkK hj
      rw [heq] at hh hr
      left
      rw [← hnm, hx]
      refine ⟨?_,?_⟩
      · have hprod : 0 ≤ a*((b*c-1)*k) := mul_nonneg ha0 (mul_nonneg (by linarith) (Nat.cast_nonneg k))
        nlinarith
      · have hcoord : signedCoordinate u (M • step e + Y (n-M)) ≤ M+a*(k+1) := by
          rw [signedCoordinate_add, signedCoordinate_nsmul]
          have hu := (le_abs_self (signedCoordinate u (step e))).trans (signedCoordinate_abs_le_norm u (step e))
          rw [latticeVector_step_norm] at hu
          have hv := (le_abs_self (signedCoordinate u (Y (n-M)))).trans (signedCoordinate_abs_le_norm u (Y (n-M)))
          have hmul := mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
          linarith
        have hheight : (M : ℝ)*dot (realPosition (step e)) ℓ+c*k-C0 ≤
            dot (realPosition (M • step e + Y (n-M))) ℓ := by
          rw [dot_realPosition_add, dot_realPosition_nsmul]
          linarith
        have hscaled := mul_le_mul_of_nonneg_left hheight (mul_nonneg ha0 hD0)
        have hDk := mul_le_mul_of_nonneg_right hDc (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        have hDM := mul_nonneg hD0 hM
        have hbase : (M : ℝ) ≤ a*(D-1) := by nlinarith [Nat.cast_nonneg M (α := ℝ)]
        have hka := mul_le_mul_of_nonneg_left hDk ha0
        have hMa := mul_nonneg ha0 hDM
        nlinarith
    · right
      have hh := (regenerationTimes_true ℓ Y hY.1 hY.2 K).2 (n-M-regenerationTimes ℓ Y K)
      change dot (realPosition (Y (regenerationTimes ℓ Y K))) ℓ ≤
        dot (realPosition (Y (regenerationTimes ℓ Y K+(n-M-regenerationTimes ℓ Y K)))) ℓ at hh
      rw [Nat.add_sub_of_le (le_of_not_gt hcut)] at hh
      have hlo := (ht K le_rfl).1
      rw [← regeneration_height_sum ℓ Y hY.1 hY.2 K] at hlo
      rw [← hnm, hx, dot_realPosition_add, dot_realPosition_nsmul]
      linarith

lemma annealed_wordCylinder_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (κ : ℝ≥0) (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x e, κ ≤ (ω x).1 e)
    (w : List (Direction d)) : (κ : ℝ≥0∞)^w.length ≤ annealedLaw ν (wordCylinder 0 w) := by
  rw [annealed_wordCylinder]
  have hconst : (κ : ℝ≥0∞)^w.length = ∫⁻ _ : Environment d, (κ : ℝ≥0∞)^w.length
      ∂environmentLaw ν := by simp
  rw [hconst]
  apply lintegral_mono_ae
  filter_upwards [hκ] with ω hω
  have hh := ENNReal.ofReal_le_ofReal (wordWeight_lower ω hω 0 w)
  simpa only [ENNReal.ofReal_pow κ.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hh

lemma annealed_eq_noDrop_mul_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    annealedLaw ν A = annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ A := by
  rw [conditionedLaw_apply_of_subset ν ℓ A hA hAD, ← mul_assoc,
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _), one_mul]

lemma forwardTemplate_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (c C C0 a : ℝ) (K M : ℕ) :
    annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M) =
      annealedLaw ν (wordCylinder 0 (List.replicate M e)) *
      annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ (WordTemplate ℓ c C C0 a K) := by
  let A := RegenerationSupport ℓ ∩ WordTemplate ℓ c C C0 a K
  have hA : MeasurableSet A := (measurableSet_regenerationSupport ℓ).inter
    (measurableSet_wordTemplate ℓ c C C0 a K)
  have hAD : A ⊆ NoDrop ℓ 0 := fun _ h => regenerationSupport_noDrop ℓ h.1
  have hrecord : ∀ y ∈ wordDepartures 0 (List.replicate M e),
      dot (realPosition y) ℓ < dot (realPosition (wordPath 0 (List.replicate M e) (List.replicate M e).length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y (List.replicate M e)).mp hy
    simp only [List.length_replicate] at hj ⊢
    rw [wordPath_replicate_prefix _ _ _ _ hj.le, wordPath_replicate,
      zero_add, zero_add, dot_realPosition_nsmul, dot_realPosition_nsmul]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) he
  have hf := annealed_record_suffix ν ℓ (List.replicate M e) hrecord A hA hAD
  simp only [List.length_replicate, wordPath_replicate, zero_add] at hf
  change annealedLaw ν (ForwardTemplate ℓ e c C C0 a K M) =
    annealedLaw ν (wordCylinder 0 (List.replicate M e)) * annealedLaw ν A at hf
  rw [hf, annealed_eq_noDrop_mul_conditioned ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)) A hA hAD, ← mul_assoc]
  congr 1
  apply measure_congr
  filter_upwards [conditioned_regenerationSupport ν ℓ htrans] with X hX
  apply propext
  change (X ∈ RegenerationSupport ℓ ∧ X ∈ WordTemplate ℓ c C C0 a K) ↔ X ∈ WordTemplate ℓ c C C0 a K
  simp only [hX,true_and]

lemma tilted_height_avoids_prefix {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (b a H : ℝ) (f Z : Path d) (n : ℕ)
    (hrecord : ∀ j < n, tiltedCoordinate ℓ u b a (f j) < tiltedCoordinate ℓ u b a (f n))
    (hf : f ∈ BoundedHeightPrefix ℓ H n)
    (hZ : ∀ k, 0 ≤ tiltedCoordinate ℓ u b a (Z k) ∨ H < dot (realPosition (Z k)) ℓ) :
    ∀ k j, j < n → f n+Z k ≠ f j := by
  intro k j hj heq
  rcases hZ k with htilt | hheight
  · have h := hrecord j hj
    rw [← heq, tiltedCoordinate_add] at h
    linarith
  · have hlo := (hf n le_rfl).1
    have hhi := (hf j hj.le).2
    rw [← heq, dot_realPosition_add] at hhi
    linarith

lemma controlled_suffix_caps_ratio {d : ℕ} (ℓ : Vector d) (u : Direction d)
    (hℓ : ∀ i, |ℓ i| ≤ 1) (b a D H t : ℝ)
    (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (ht : 0 < t)
    (f X : Path d) (n : ℕ) (hf : f ∈ FirstRatioExceed ℓ u b a H t n)
    (hX : X ∈ pathCylinder f n)
    (hcontrol : ∀ k, (signedCoordinate u (X (n+k)-f n) ≤
      a*D*(1+dot (realPosition (X (n+k)-f n)) ℓ)) ∨
      H < dot (realPosition (X (n+k)-f n)) ℓ) :
    X ∉ RatioHit ℓ u b a H (t+(2*b+1+D)) := by
  intro hhit
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hhit
  have ha0 : 0 < a := by linarith
  have hscale : 0 ≤ a*D := mul_nonneg ha0.le hD
  by_cases hkn : k < n
  · have he := heightRatio_congr ℓ u b a k (fun j hj => hX j (by omega))
    have hlo := hf.2 k hkn
    have hkbound : t+(2*b+1+D) < heightRatio ℓ u b a X k := hk.2
    rw [he] at hkbound
    linarith [show 0 ≤ 2*b+1+D by linarith]
  · have hnk : n ≤ k := by omega
    have hkm : n+(k-n) = k := Nat.add_sub_of_le hnk
    have hz := hcontrol (k-n)
    rw [hkm, dot_realPosition_sub] at hz
    have hlaunch := (hf.1.1.2 n le_rfl).1
    have htop := (hk.1.2 k le_rfl).2
    rcases hz with hcoord | hhigh
    · have hs : signedCoordinate u (X k) = signedCoordinate u (f n) +
          signedCoordinate u (X k-f n) := by
        rw [← signedCoordinate_add]
        congr 1
        abel
      have hratio := firstRatioExceed_overshoot ℓ u hℓ b a H t hb ha ht f n hf
      have denom (j : ℕ) : 0 < a*(1+runningHeight ℓ X j) :=
        mul_pos ha0 (by linarith [runningHeight_nonneg ℓ X j])
      have hne : runningHeight ℓ f n = runningHeight ℓ X n :=
        runningHeight_congr ℓ n (fun j hj => (hX j hj).symm)
      have hm := runningHeight_mono ℓ X hnk
      have hheight := height_le_runningHeight ℓ X (show k ≤ k from le_rfl)
      have hprev : signedCoordinate u (f n) ≤ (t+b+1)*(a*(1+runningHeight ℓ X n)) := by
        have hfden : 0 < a*(1+runningHeight ℓ f n) := by rw [hne]; exact denom n
        have hh := (div_le_iff₀ hfden).mp hratio
        dsimp only [heightRatio, tiltedCoordinate] at hh
        rw [hne] at hh
        have hpos := mul_nonneg (mul_nonneg hb ha0.le) hlaunch
        linarith
      have hlaunchscale := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (t+b+1)*a by positivity)
      have hrelscale := mul_le_mul_of_nonneg_left (show 1+dot (realPosition (X k)) ℓ -
          dot (realPosition (f n)) ℓ ≤ 1+runningHeight ℓ X k by linarith) hscale
      have hheightscale := mul_le_mul_of_nonneg_left hheight (mul_nonneg hb ha0.le)
      have hbound : heightRatio ℓ u b a X k ≤ t+(2*b+1+D) := by
        apply (div_le_iff₀ (denom k)).mpr
        dsimp only [tiltedCoordinate]
        nlinarith
      exact (not_le_of_gt hk.2) hbound
    · linarith

lemma prefix_favourable_gain {d : ℕ} (μ : Measure (Path d))
    (E B : Set (Path d)) (n : ℕ) (p : ℝ≥0∞)
    (hE : PrefixDetermined n E)
    (hfav : ∀ f ∈ E, ∃ A : Set (Path d), MeasurableSet A ∧ A ⊆ pathCylinder f n ∧
      Disjoint B A ∧ μ A = μ (pathCylinder f n)*p) :
    μ (B∩E)+μ E*p ≤ μ E := by
  classical
  rw [measure_partition_prefix μ (B∩E) n, measure_partition_prefix μ E n,
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro f
  let g := extendPrefix n f
  by_cases hg : g ∈ E
  · obtain ⟨A,hA,hAC,hBA,hm⟩ := hfav g hg
    have hc : E ∩ pathCylinder g n = pathCylinder g n := by
      rw [prefixDetermined_inter_cylinder E n hE g, ite_eq_left hg]
    have he : (B∩E)∩pathCylinder g n = B∩pathCylinder g n := by rw [Set.inter_assoc, hc]
    change μ ((B∩E)∩pathCylinder g n)+μ (E∩pathCylinder g n)*p ≤ μ (E∩pathCylinder g n)
    rw [he,hc,← hm]
    have hd : Disjoint (B∩pathCylinder g n) A := hBA.mono_left Set.inter_subset_left
    rw [← measure_union hd hA]
    exact measure_mono (Set.union_subset Set.inter_subset_right hAC)
  · have hc : E∩pathCylinder g n = ∅ := by
      rw [prefixDetermined_inter_cylinder E n hE g, ite_eq_right hg]
    have he : (B∩E)∩pathCylinder g n = ∅ := by rw [Set.inter_assoc,hc,Set.inter_empty]
    change μ ((B∩E)∩pathCylinder g n)+μ (E∩pathCylinder g n)*p ≤ μ (E∩pathCylinder g n)
    rw [he,hc,measure_empty,zero_mul,zero_add]

lemma stopping_prefix_favourable_gain {d : ℕ} (μ : Measure (Path d))
    (E : ℕ → Set (Path d)) (B : Set (Path d)) (p : ℝ≥0∞)
    (hE : ∀ n, PrefixDetermined n (E n)) (hm : ∀ n, MeasurableSet (E n))
    (hd : Pairwise (fun n m => Disjoint (E n) (E m))) (hB : MeasurableSet B)
    (hsub : B ⊆ ⋃ n,E n)
    (hfav : ∀ n f, f ∈ E n → ∃ A : Set (Path d), MeasurableSet A ∧ A ⊆ pathCylinder f n ∧
      Disjoint B A ∧ μ A = μ (pathCylinder f n)*p) :
    μ B+μ (⋃ n,E n)*p ≤ μ (⋃ n,E n) := by
  have hBu : B = ⋃ n,B∩E n := by
    ext X
    simp only [Set.mem_iUnion,Set.mem_inter_iff]
    exact ⟨fun h => by obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hsub h); exact ⟨n,h,hn⟩,
      fun ⟨_,h,_⟩ => h⟩
  have hdb : Pairwise (fun n m => Disjoint (B∩E n) (B∩E m)) :=
    fun n m hnm => (hd hnm).mono Set.inter_subset_right Set.inter_subset_right
  rw [hBu,measure_iUnion hdb (fun n => hB.inter (hm n)),
    measure_iUnion hd hm,← ENNReal.tsum_mul_right,← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun n => prefix_favourable_gain μ (E n) B n p (hE n) (hfav n)

lemma ratio_threshold_contraction {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (u : Direction d) (hℓ : ∀ i, |ℓ i| ≤ 1)
    (b a D H t : ℝ) (hb : 0 ≤ b) (ha : 1 ≤ a) (hD : 0 ≤ D) (ht : 0 < t)
    (A : Set (Path d)) (hA : MeasurableSet A)
    (hcontrol : ∀ Z ∈ A, ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k) ∧
      signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨
      H < dot (realPosition (Z k)) ℓ) :
    (annealedLaw ν).real (RatioHit ℓ u b a H (t+(2*b+1+D))) ≤
      (1-(annealedLaw ν).real A)*(annealedLaw ν).real (RatioHit ℓ u b a H t) := by
  let μ := annealedLaw ν
  let B := RatioHit ℓ u b a H (t+(2*b+1+D))
  have hsub : B ⊆ ⋃ n, FirstRatioExceed ℓ u b a H t n := by
    rw [← ratioHit_eq_first]
    exact ratioHit_antitone ℓ u b a H (by linarith)
  have hg := stopping_prefix_favourable_gain μ (FirstRatioExceed ℓ u b a H t) B (μ A)
    (prefixDetermined_firstRatioExceed ℓ u b a H t)
    (measurableSet_firstRatioExceed ℓ u b a H t)
    (firstRatioExceed_disjoint ℓ u b a H t)
    (measurableSet_ratioHit ℓ u b a H _) hsub (by
      intro n f hf
      let F := (fun X : Path d => fun k => X (n+k)-f n) ⁻¹' A ∩ pathCylinder f n
      have hF : MeasurableSet F := (hA.preimage (by fun_prop)).inter (measurableSet_pathCylinder f n)
      obtain ⟨hn,hrecord⟩ := firstRatioExceed_record ℓ u b a H t (by linarith) ht f n hf
      refine ⟨F,hF,Set.inter_subset_right,?_,?_⟩
      · apply Set.disjoint_left.mpr
        intro X hB hF
        apply controlled_suffix_caps_ratio ℓ u hℓ b a D H t hb ha hD ht f X n hf hF.2
        · intro k
          rcases hcontrol _ hF.1 k with h | h
          · exact Or.inl h.2
          · exact Or.inr h
        · exact hB
      · exact annealed_prefix_avoiding_suffix ν f n hn A hA
          (fun j hj he => by have hh := hrecord j hj; rw [he] at hh; exact (lt_irrefl _) hh)
          (fun Z hZ => tilted_height_avoids_prefix ℓ u b a H f Z n hrecord hf.1.1.2
            (fun k => (hcontrol Z hZ k).imp And.left id)))
  rw [← ratioHit_eq_first] at hg
  have hpne : μ (RatioHit ℓ u b a H t)*μ A ≠ ∞ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hg
  rw [ENNReal.toReal_add (measure_ne_top _ _) hpne,ENNReal.toReal_mul] at hr
  change (μ B).toReal ≤ (1-(μ A).toReal)*(μ (RatioHit ℓ u b a H t)).toReal
  nlinarith

end DirectionalTransience
end
end

end OAI
