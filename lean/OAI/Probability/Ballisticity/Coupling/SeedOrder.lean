import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma ae_at_atom {A : Type*} [MeasurableSpace A] {μ : Measure A} {P : A → Prop}
    (h : ∀ᵐ x ∂μ, P x) {x : A} (hx : μ {x} ≠ 0) : P x := by
  by_contra hnot
  exact hx (measure_mono_null (by simpa only [Set.singleton_subset_iff,Set.mem_ofPred_eq] using hnot) (ae_iff.mp h))

lemma atom_of_ae_domination {A : Type*} [MeasurableSpace A] (μ ρ : Measure A)
    (c : ℝ≥0∞) (hc : c ≠ 0) (h : c • μ ≤ ρ) {x : A} (hx : μ {x} ≠ 0) : ρ {x} ≠ 0 := by
  intro hz
  have hh := h {x}
  simp only [Measure.smul_apply,smul_eq_mul,hz,nonpos_iff_eq_zero,mul_eq_zero] at hh
  exact hh.elim hc hx

lemma seedEndpointRaw_atom_origin {d : ℕ} (e : Direction d) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : Measure (Lattice d)) (ω : Environment d)
    (y : Lattice d) (hy : seedEndpointRaw e H R μ ω {y} ≠ 0) :
    ∃ x, μ {x} ≠ 0 ∧ R x y := by
  by_contra! hn
  apply hy
  rw [seedEndpointRaw_apply,lintegral_countable']
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  by_cases hx : μ {x}=0
  · simp [hx]
  · have hxy := hn x hx
    have he : {y} ∩ {z | R x z}=∅ := by ext z; simp only [Set.mem_inter_iff,Set.mem_singleton_iff,Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]; rintro ⟨rfl,h⟩; exact hxy h
    simp [he]

lemma seedAdvance_atom_origin {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ)
    (R : Lattice d → Lattice d → Prop) (μ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H R μ.measure ω Set.univ ≠ 0)
    (y : Lattice d) (hy : (seedAdvance e a H R μ ω).measure {y} ≠ 0) :
    ∃ x, μ.measure {x} ≠ 0 ∧ R x y := by
  apply seedEndpointRaw_atom_origin e H R μ.measure ω y
  rw [←seedAdvance_mass e a H R μ ω,Measure.smul_apply,smul_eq_mul]
  exact mul_ne_zero hm hy

lemma seedHalfProfile_atom_origin {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ : SeedProfile e a) (x : Lattice d)
    (hx : (seedHalfProfile e f a s upper μ).measure {x} ≠ 0) :
    μ.measure {x} ≠ 0 ∧
      (if upper then seedMedian f s μ.val ≤ s*signedHeight f x
       else s*signedHeight f x ≤ seedMedian f s μ.val) := by
  exact ⟨atom_of_ae_domination _ _ _ (by norm_num) (seedHalf_domination f s upper μ.val) hx,
    ae_at_atom (seedHalf_ae f s upper μ.val) hx⟩

def SeedOrdered {d : ℕ} (f : Direction d) (s : ℤ) (g : ℝ)
    (μ ρ : Measure (Lattice d)) : Prop :=
  ∀ x, μ {x} ≠ 0 → ∀ y, ρ {y} ≠ 0 →
    g ≤ (s:ℝ)*(signedCoordinate f y-signedCoordinate f x)

lemma seedOrdered_mono {d : ℕ} (f : Direction d) (s : ℤ) {g g' : ℝ}
    {μ ρ : Measure (Lattice d)} (h : SeedOrdered f s g μ ρ) (hg : g' ≤ g) : SeedOrdered f s g' μ ρ :=
  fun x hx y hy => hg.trans (h x hx y hy)

lemma seedOrdered_central {d : ℕ} (e f : Direction d) (a s : ℤ) (H : ℕ)
    (θ z g : ℝ) (hs : s=1 ∨ s= -1) (μ ρ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H (SeedCentral f H θ z) μ.measure ω Set.univ ≠ 0)
    (hr : seedEndpointRaw e H (SeedCentral f H θ z) ρ.measure ω Set.univ ≠ 0)
    (ho : SeedOrdered f s g μ.measure ρ.measure) :
    SeedOrdered f s (g-2*z) (seedAdvance e a H (SeedCentral f H θ z) μ ω).measure
      (seedAdvance e a H (SeedCentral f H θ z) ρ ω).measure := by
  intro x hx y hy
  obtain ⟨u,hu,hux⟩ := seedAdvance_atom_origin e a H _ μ ω hm x hx
  obtain ⟨v,hv,hvy⟩ := seedAdvance_atom_origin e a H _ ρ ω hr y hy
  have huv := ho u hu v hv
  simp only [SeedCentral,signedCoordinate_sub,abs_le] at hux hvy
  rcases hs with rfl | rfl <;> norm_num at huv ⊢ <;> linarith [hux.1,hux.2,hvy.1,hvy.2]

lemma signedHeight_cast_coordinate {d : ℕ} (f : Direction d) (x : Lattice d) :
    (signedHeight f x:ℝ)=signedCoordinate f x := by
  simp only [signedHeight,signedCoordinate,Int.cast_ite,Int.cast_neg]

lemma seedOrdered_split {d : ℕ} (e f : Direction d) (a s : ℤ) (H : ℕ)
    (θ z b : ℝ) (hs : s=1 ∨ s= -1) (μ : SeedProfile e a) (ω : Environment d)
    (hm : seedEndpointRaw e H (SeedCentral f H θ z) (seedHalfProfile e f a s false μ).measure ω Set.univ ≠ 0)
    (hr : seedEndpointRaw e H (SeedJump f H s θ b) (seedHalfProfile e f a s true μ).measure ω Set.univ ≠ 0) :
    SeedOrdered f s (b-z)
      (seedAdvance e a H (SeedCentral f H θ z) (seedHalfProfile e f a s false μ) ω).measure
      (seedAdvance e a H (SeedJump f H s θ b) (seedHalfProfile e f a s true μ) ω).measure := by
  intro x hx y hy
  obtain ⟨u,hu,hux⟩ := seedAdvance_atom_origin e a H _ _ ω hm x hx
  obtain ⟨v,hv,hvy⟩ := seedAdvance_atom_origin e a H _ _ ω hr y hy
  have hlu := (seedHalfProfile_atom_origin e f a s false μ u hu).2
  have hlv := (seedHalfProfile_atom_origin e f a s true μ v hv).2
  simp only [Bool.false_eq_true,↓reduceIte] at hlu
  simp only [↓reduceIte] at hlv
  have ho : (s:ℝ)*signedCoordinate f u ≤ (s:ℝ)*signedCoordinate f v := by
    simpa only [Int.cast_mul,signedHeight_cast_coordinate] using (show ((s*signedHeight f u:ℤ):ℝ) ≤ ((s*signedHeight f v:ℤ):ℝ) from by exact_mod_cast hlu.trans hlv)
  simp only [SeedCentral,signedCoordinate_sub,abs_le] at hux
  simp only [SeedJump,signedCoordinate_sub] at hvy
  rcases hs with rfl | rfl <;> norm_num at ho hvy ⊢ <;> linarith [hux.1,hux.2]

lemma seedOrdered_half_left {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ ρ : SeedProfile e a) (g : ℝ) (ho : SeedOrdered f s g μ.measure ρ.measure) :
    SeedOrdered f s g (seedHalfProfile e f a s upper μ).measure ρ.measure :=
  fun x hx y hy => ho x (seedHalfProfile_atom_origin e f a s upper μ x hx).1 y hy

lemma seedOrdered_half_right {d : ℕ} (e f : Direction d) (a s : ℤ) (upper : Bool)
    (μ ρ : SeedProfile e a) (g : ℝ) (ho : SeedOrdered f s g μ.measure ρ.measure) :
    SeedOrdered f s g μ.measure (seedHalfProfile e f a s upper ρ).measure :=
  fun x hx y hy => ho x hx y (seedHalfProfile_atom_origin e f a s upper ρ y hy).1

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev SeedState {d : ℕ} (e : Direction d) (a : ℤ) := ℕ × (ℕ → SeedProfile e a)

lemma measurable_seedEval {d : ℕ} (e : Direction d) (a : ℤ) :
    Measurable (fun p : (ℕ → SeedProfile e a) × ℕ => p.1 p.2) :=
  measurable_from_prod_countable_left fun n => measurable_pi_apply n

noncomputable def seedCentralInput {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) : SeedProfile e a :=
  if q.1 < k ∧ i=q.1-1 then seedHalfProfile e f a s false (q.2 i) else q.2 i

noncomputable def seedJumpInput {d : ℕ} (e f : Direction d) (a s : ℤ)
    (q : SeedState e a) : SeedProfile e a := seedHalfProfile e f a s true (q.2 (q.1-1))

lemma measurable_seedCentralInput {d : ℕ} (e f : Direction d) (a s : ℤ) (k i : ℕ) :
    Measurable (fun q : SeedState e a => seedCentralInput e f a s k q i) := by
  unfold seedCentralInput
  exact (((measurable_seedHalfProfile e f a s false).comp ((measurable_pi_apply i).comp measurable_snd))).ite
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_eq_fun measurable_const (measurable_fst.sub_const 1)))
    ((measurable_pi_apply i).comp measurable_snd)

lemma measurable_seedJumpInput {d : ℕ} (e f : Direction d) (a s : ℤ) :
    Measurable (seedJumpInput e f a s) := by
  apply (measurable_seedHalfProfile e f a s true).comp
  exact (measurable_seedEval e a).comp (measurable_snd.prodMk (measurable_fst.sub_const 1))

noncomputable def seedSplitTest {d : ℕ} (e f : Direction d) (a s : ℤ) (H : ℕ)
    (θ b j : ℝ) (q : SeedState e a) (ω : Environment d) : Prop :=
  j ≤ (seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s q).measure ω Set.univ).toReal

noncomputable def seedStateStep {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) : SeedState e (a+H) :=
  let split := q.1<k ∧ seedSplitTest e f a s H θ b j q ω
  (if split then q.1+1 else q.1,
   fun i => if split ∧ i=q.1 then seedAdvance e a H (SeedJump f H s θ b) (seedJumpInput e f a s q) ω
     else seedAdvance e a H (SeedCentral f H θ z) (seedCentralInput e f a s k q i) ω)

def SeedStateOrdered {d : ℕ} (f : Direction d) (s : ℤ) (g : ℝ) {e : Direction d} {a : ℤ}
    (q : SeedState e a) : Prop := ∀ i j, i < j → j < q.1 → SeedOrdered f s g (q.2 i).measure (q.2 j).measure

def SeedStateRetained {d : ℕ} (e : Direction d) (a : ℤ) (H : ℕ) (π : Measure (Lattice d))
    (ω : Environment d) (δ : ℝ≥0∞) (q : SeedState e a) : Prop :=
  ∀ i < q.1, δ • (q.2 i).measure ≤ seedEndpointRaw e H (fun _ _ => True) π ω

noncomputable def SeedPreserved {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z c : ℝ) (q : SeedState e a) (ω : Environment d) : Prop :=
  ∀ i < q.1, c ≤ (seedEndpointRaw e H (SeedCentral f H θ z)
    (seedCentralInput e f a s k q i).measure ω Set.univ).toReal

lemma seedStateStep_count {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) :
    q.1 ≤ (seedStateStep e f a s k H θ z b j q ω).1 ∧
    (seedStateStep e f a s k H θ z b j q ω).1 ≤ q.1+1 ∧
    (q.1≤k → (seedStateStep e f a s k H θ z b j q ω).1≤k) := by
  simp only [seedStateStep]
  split_ifs <;> omega

lemma seedStateStep_strict {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) (hq : q.1<k)
    (ht : seedSplitTest e f a s H θ b j q ω) :
    q.1 < (seedStateStep e f a s k H θ z b j q ω).1 := by
  simp [seedStateStep,hq,ht]

lemma seedCentralInput_domination {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) :
    (1/2:ℝ≥0∞) • (seedCentralInput e f a s k q i).measure ≤ (q.2 i).measure := by
  unfold seedCentralInput
  split_ifs
  · exact seedHalf_domination f s false (q.2 i).val
  · intro U
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_of_le_one_left bot_le (by norm_num)

lemma seedCentralInput_atom {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ)
    (q : SeedState e a) (i : ℕ) {x : Lattice d}
    (hx : (seedCentralInput e f a s k q i).measure {x} ≠ 0) : (q.2 i).measure {x} ≠ 0 :=
  atom_of_ae_domination _ _ _ (by norm_num) (seedCentralInput_domination e f a s k q i) hx

lemma seedStateStep_retained {d : ℕ} (e f : Direction d) (a s : ℤ) (k H h : ℕ)
    (θ z b j c : ℝ) (q : SeedState e a) (ω : Environment d) (π : Measure (Lattice d))
    (δ : ℝ≥0∞) (hq : 0 < q.1) (hj : 0 ≤ j) (hc : 0 ≤ c)
    (hr : SeedStateRetained e a h π ω δ q)
    (hp : SeedPreserved e f a s k H θ z c q ω) :
    SeedStateRetained e (a+H) (h+H) π ω (δ*(ENNReal.ofReal (min c j)/2))
      (seedStateStep e f a s k H θ z b j q ω) := by
  intro i hi
  have hcentral (i : ℕ) (hi : i<q.1) :
      (δ*(ENNReal.ofReal (min c j)/2)) •
        (seedAdvance e a H (SeedCentral f H θ z) (seedCentralInput e f a s k q i) ω).measure ≤
          seedEndpointRaw e (h+H) (fun _ _ => True) π ω := by
    have hsub : (δ/2) • (seedCentralInput e f a s k q i).measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω := by
      calc
        _ = δ • ((1/2:ℝ≥0∞) • (seedCentralInput e f a s k q i).measure) := by rw [smul_smul]; congr 1; simp [div_eq_mul_inv]
        _ ≤ δ • (q.2 i).measure := by
          intro U; simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul_right (seedCentralInput_domination e f a s k q i U) δ
        _ ≤ _ := hr i hi
    have hmass : ENNReal.ofReal (min c j) ≤ seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ := by
      apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
      rw [ENNReal.toReal_ofReal (le_min hc hj)]
      exact (min_le_left _ _).trans (hp i hi)
    have hh := seedAdvance_retained e a h H _ π (seedCentralInput e f a s k q i) ω (δ/2) (ENNReal.ofReal (min c j)) hsub hmass
    convert hh using 1
    simp [div_eq_mul_inv,mul_comm,mul_left_comm]
  by_cases ht : q.1<k ∧ seedSplitTest e f a s H θ b j q ω
  · simp only [seedStateStep,ite_eq_left ht] at hi ⊢
    by_cases he : i=q.1
    · simp only [he]
      have hsub : (δ/2) • (seedJumpInput e f a s q).measure ≤ seedEndpointRaw e h (fun _ _ => True) π ω := by
        calc
          _ = δ • ((1/2:ℝ≥0∞) • (seedJumpInput e f a s q).measure) := by rw [smul_smul]; congr 1; simp [div_eq_mul_inv]
          _ ≤ δ • (q.2 (q.1-1)).measure := by
            intro U; simpa only [Measure.smul_apply,smul_eq_mul,seedJumpInput,seedHalfProfile,SeedProfile.measure] using mul_le_mul_right (seedHalf_domination f s true (q.2 (q.1-1)).val U) δ
          _ ≤ _ := hr (q.1-1) (by omega)
      have hmass : ENNReal.ofReal (min c j) ≤ seedEndpointRaw e H (SeedJump f H s θ b) (seedJumpInput e f a s q).measure ω Set.univ := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans ht.2)
      have hh := seedAdvance_retained e a h H _ π (seedJumpInput e f a s q) ω (δ/2) (ENNReal.ofReal (min c j)) hsub hmass
      simpa [seedStateStep,ht,he,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
    · simp only [he,and_false,ite_false]
      exact hcentral i (by omega)
  · simp only [seedStateStep,ite_eq_right ht] at hi ⊢
    simpa [seedStateStep,ht] using hcentral i hi

end DirectionalTransience

end

end OAI
