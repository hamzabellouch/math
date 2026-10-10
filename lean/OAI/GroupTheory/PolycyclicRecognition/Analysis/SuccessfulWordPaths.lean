import OAI.GroupTheory.PolycyclicRecognition.Analysis.ParametrizedSupportPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SwitchEndpoints

namespace OAI

/-! # Prescribed word paths through the successful sheets -/

noncomputable section

namespace PolycyclicRecognition

variable {G : Type*} [Group G]

/-- All the states at which a support leg is traversed are in the good set. -/
def WordSheetsGood (A : Set G) : G → List G → Prop
  | n, [] => n ∈ A
  | n, g :: u => n ∈ A ∧ WordSheetsGood A (n * g) u

theorem WordSheetsGood.start {A : Set G} {n : G} {u : List G}
    (h : WordSheetsGood A n u) : n ∈ A := by
  cases u with
  | nil => exact h
  | cons g u => exact h.1

/-- The independent-switch event is exactly the good-sheet condition used
by the geometric word paths, after adjoining the initial good sheet. -/
theorem wordSheetsGood_of_switchSuccessful (A : Set G) (m : ℕ)
    (p : Fin m → G × G) (n : G) (hn : n ∈ A) (j : ℕ)
    (hs : SwitchSuccessful (fun _ => A) j m n (vectorSwitchParameters m p)) :
    WordSheetsGood A n (List.ofFn (fun i => (p i).1 * (p i).2⁻¹)) := by
  induction m generalizing j n with
  | zero => exact hn
  | succ m ih =>
    rw [List.ofFn_succ]
    refine ⟨hn, ?_⟩
    have hs' : n * (p 0).1 * (p 0).2⁻¹ ∈ A ∧
        SwitchSuccessful (fun _ => A) (j + 1) m (n * (p 0).1 * (p 0).2⁻¹)
          (vectorSwitchParameters m (fun i => p i.succ)) := hs
    simpa only [mul_assoc] using ih (fun i => p i.succ) (n * (p 0).1 * (p 0).2⁻¹)
      hs'.1 (j + 1) hs'.2

/-- Apply the successful-event interpretation to the original real samples. -/
theorem wordSheetsGood_sampled (A : Set G) (f : ℕ → ℝ → G)
    (hf : ∀ j s t, f j s * (f j t)⁻¹ = f j (s - t)) (m : ℕ)
    (t : Fin (m + m) → ℝ) (n : G) (hn : n ∈ A)
    (hs : SwitchSuccessful (fun _ => A) 0 m n (sampledSwitchParameters f m t)) :
    WordSheetsGood A n (List.ofFn (fun j : Fin m =>
      f j.val (t (Fin.castAdd m j) - t (Fin.natAdd m j)))) := by
  unfold sampledSwitchParameters flatSwitchSamples at hs
  rw [mapSwitchParameters_vector] at hs
  have hh := wordSheetsGood_of_switchSuccessful A m
    (fun j => (f (0 + j.val) (flatSamplePairs m t j).1,
      f (0 + j.val) (flatSamplePairs m t j).2)) n hn 0 hs
  simpa only [Nat.zero_add, flatSamplePairs, hf] using hh

variable [PseudoMetricSpace G] [IsTopologicalGroup G]
  {I : Type*} (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1) (d₀ : G) (r : ℝ)

/-- Concatenation only asks for the good states actually visited by this
word. The observable range need not be defined by a homomorphism. -/
theorem supportWordPath_good_bound (A S : Set G) (P : I → ℝ → Prop)
    {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i b, P i b → n * f i b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b t ∈ S)
    (u : List (I × ℝ)) (hu : ∀ z ∈ u, P z.1 z.2) (n : G)
    (hgood : WordSheetsGood A n (u.map (fun z => f z.1 z.2))) :
    PathMetricBound (supportWordPath d f hd hf hd₀ hf₀ d₀ r u n)
      (L * 2 ^ u.length) (κ * 2 ^ u.length) ∧
      ∀ t, supportWordPath d f hd hf hd₀ hf₀ d₀ r u n t ∈ S := by
  induction u generalizing n with
  | nil =>
    constructor
    · intro s t
      change dist (n * d₀) (n * d₀) ≤ _
      simp only [dist_self, List.length_nil, pow_zero, mul_one]
      positivity
    · exact fun _ => hbase n hgood
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hg : n ∈ A ∧ WordSheetsGood A (n * f i b) (u.map (fun z => f z.1 z.2)) := hgood
    have hu' : ∀ z ∈ u, P z.1 z.2 := fun z hz => hu z (List.mem_cons_of_mem _ hz)
    obtain ⟨hp, hpS⟩ := hstep n hg.1 i b (hu (i, b) List.mem_cons_self) hg.2.start
    obtain ⟨hq, hqS⟩ := ih hu' (n * f i b) hg.2
    have hpow : 1 ≤ (2 : ℝ) ^ u.length := one_le_pow₀ (by norm_num)
    have hp' := hp.mono
      (show L ≤ L * 2 ^ u.length by nlinarith)
      (show κ ≤ κ * 2 ^ u.length by nlinarith)
    constructor
    · have hb := hp'.trans (mul_nonneg hκ (by positivity)) hq
      have he : n * indexedWordProduct f ((i, b) :: u) * d₀ =
          (n * f i b) * indexedWordProduct f u * d₀ := by
        simp [indexedWordProduct, mul_assoc]
      have hb' := hb.cast rfl he
      convert hb' using 1 <;>
        first | rfl | (simp only [List.length_cons, pow_succ]; ring)
    · exact path_trans_range_mem hpS hqS

end PolycyclicRecognition

end

end OAI
