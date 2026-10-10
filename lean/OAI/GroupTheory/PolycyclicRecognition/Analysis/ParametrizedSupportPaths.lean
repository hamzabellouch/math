import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitPaths

namespace OAI

/-! # Continuous sampling of prescribed generator words

When the generator indices are fixed and the amplitudes depend continuously
on a parameter, every fixed time sample of the explicitly constructed path
is continuous in that parameter. This retains the measurability needed for
stationary endpoint averaging.
-/

noncomputable section

namespace PolycyclicRecognition

variable {G I : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  (d f : I → ℝ → G) (hd : ∀ i, Continuous (d i)) (hf : ∀ i, Continuous (f i))
  (hd₀ : ∀ i, d i 0 = 1) (hf₀ : ∀ i, f i 0 = 1)
  (d₀ : G) (r : ℝ)

def indexedWordProduct (u : List (I × ℝ)) : G :=
  (u.map (fun z => f z.1 z.2)).prod

def supportWordPath : (u : List (I × ℝ)) → (n : G) →
    Path (n * d₀) (n * indexedWordProduct f u * d₀)
  | [], n => (Path.refl (n * d₀)).cast rfl (by simp [indexedWordProduct])
  | (i, b) :: u, n =>
    ((supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) n d₀ r b).trans
      (supportWordPath u (n * f i b))).cast rfl (by simp [indexedWordProduct, mul_assoc])

/-- Fixed-time samples of a word path are continuous under continuous
variation of its amplitudes and its initial sheet. -/
theorem continuous_supportWordPath_sample
    {Y : Type*} [TopologicalSpace Y] (w : List (I × (Y → ℝ)))
    (hw : ∀ z ∈ w, Continuous z.2) (n : Y → G) (hn : Continuous n)
    (t : unitInterval) :
    Continuous (fun y => supportWordPath d f hd hf hd₀ hf₀ d₀ r
      (w.map (fun z => (z.1, z.2 y))) (n y) t) := by
  induction w generalizing n t with
  | nil =>
    change Continuous (fun y => n y * d₀)
    exact hn.mul_const d₀
  | cons z w ih =>
    rcases z with ⟨i, b⟩
    have hb : Continuous b := hw (i, b) List.mem_cons_self
    have hw' : ∀ z ∈ w, Continuous z.2 := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    change Continuous (fun y =>
      ((supportVisitPath (d i) (hd i) (hd₀ i) (f i) (hf i) (hf₀ i) (n y) d₀ r (b y)).trans
        (supportWordPath d f hd hf hd₀ hf₀ d₀ r
          (w.map (fun z => (z.1, z.2 y))) (n y * f i (b y)))) t)
    apply continuous_path_trans_sample
    · intro u
      exact continuous_supportVisitPath_sample (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n hn b hb d₀ r u
    · intro u
      exact ih hw' (fun y => n y * f i (b y)) (hn.mul ((hf i).comp hb)) u

/-- The explicit word path retains the uniform metric and range bounds of
its actual single-letter visits. -/
theorem supportWordPath_bound
    {W : Type*} [AddCommGroup W] (π : G →* Multiplicative W)
    (P : I → ℝ → Prop) (hπf : ∀ i b, P i b → π (f i b) = 1)
    {S : Set G} (hbase : ∀ n, π n = 1 → n * d₀ ∈ S)
    {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hstep : ∀ n, π n = 1 → ∀ i b, P i b →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b) L κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (f i) (hf i) (hf₀ i) n d₀ r b t ∈ S)
    (u : List (I × ℝ)) (hu : ∀ z ∈ u, P z.1 z.2) (n : G) (hn : π n = 1) :
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
    · exact fun _ => hbase n hn
  | cons z u ih =>
    rcases z with ⟨i, b⟩
    have hi := hu (i, b) List.mem_cons_self
    have hu' : ∀ z ∈ u, P z.1 z.2 := fun z hz => hu z (List.mem_cons_of_mem _ hz)
    obtain ⟨hp, hpS⟩ := hstep n hn i b hi
    have hn' : π (n * f i b) = 1 := by rw [map_mul, hn, hπf i b hi, one_mul]
    obtain ⟨hq, hqS⟩ := ih hu' (n * f i b) hn'
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
