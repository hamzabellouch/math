import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.GrowingFiltrationMartingale

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  {P : Measure Ω} [IsFiniteMeasure P]

theorem tendsto_condExp_growing_L1
    (G : Filtration ℕ mΩ) {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Integrable (X n) P) (hY : Integrable Y P)
    (hlim : Tendsto (fun n => eLpNorm (X n - Y) 1 P) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (P[X n | G n] - P[Y | ⨆ n, G n]) 1 P) atTop (𝓝 0) := by
  have hlevy := tendsto_eLpNorm_condExp (μ := P) (ℱ := G) Y
  have hsum := hlim.add hlevy
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  have hdiff : eLpNorm (P[X n | G n] - P[Y | G n]) 1 P ≤
      eLpNorm (X n - Y) 1 P := by
    rw [← eLpNorm_congr_ae (condExp_sub (hX n) hY (G n))]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  have heq : P[X n | G n] - P[Y | ⨆ n, G n] =
      (P[X n | G n] - P[Y | G n]) + (P[Y | G n] - P[Y | ⨆ n, G n]) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  dsimp only
  rw [heq]
  exact (eLpNorm_add_le le_rfl).trans
    (add_le_add hdiff le_rfl)

theorem martingale_of_growing_filtration_L1_limits
    (F : ℕ → Filtration ι mΩ) (G : Filtration ι mΩ)
    (hmono : ∀ t, Monotone (fun n => F n t))
    (hsup : ∀ t, (⨆ n, F n t) = G t)
    {X : ℕ → ι → Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : ∀ n, Martingale (X n) (F n) P)
    (hY : StronglyAdapted G Y) (hYint : ∀ t, Integrable (Y t) P)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 1 P) atTop (𝓝 0)) :
    Martingale Y G P := by
  refine ⟨hY, ?_⟩
  intro s t hst
  let E : Filtration ℕ mΩ :=
    ⟨fun n => F n s, hmono s, fun n => (F n).le s⟩
  have hce := tendsto_condExp_growing_L1 E
    (fun n => (hX n).integrable t) (hYint t) (hlim t)
  change Tendsto (fun n => eLpNorm
    (P[X n t | F n s] - P[Y t | ⨆ n, F n s]) 1 P) atTop (𝓝 0) at hce
  rw [hsup s] at hce
  have hce' : Tendsto (fun n => eLpNorm (X n s - P[Y t | G s]) 1 P)
      atTop (𝓝 0) := by
    apply hce.congr
    intro n
    exact eLpNorm_congr_ae (((hX n).condExp_ae_eq hst).sub EventuallyEq.rfl)
  have hb (n : ℕ) : eLpNorm (P[Y t | G s] - Y s) 1 P ≤
      eLpNorm (X n s - P[Y t | G s]) 1 P + eLpNorm (X n s - Y s) 1 P := by
    have heq : P[Y t | G s] - Y s =
        (P[Y t | G s] - X n s) + (X n s - Y s) := by
      funext ω
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [heq]
    have hbound := eLpNorm_add_le (μ := P) (f := P[Y t | G s] - X n s)
      (g := X n s - Y s) (p := 1) le_rfl
    simpa only [eLpNorm_sub_comm (P[Y t | G s]) (X n s)] using hbound
  have hz : eLpNorm (P[Y t | G s] - Y s) 1 P = 0 := by
    apply le_antisymm ?_ bot_le
    have hsum := hce'.add (hlim s)
    simp only [add_zero] at hsum
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hsum (Eventually.of_forall hb)
  exact (sub_ae_eq_zero _ _).mp ((eLpNorm_eq_zero_iff (by norm_num)).mp hz)

theorem compensatedSquare_of_growing_limits
    (F : ℕ → Filtration ι mΩ) (G : Filtration ι mΩ)
    (hmono : ∀ t, Monotone (fun n => F n t))
    (hsup : ∀ t, (⨆ n, F n t) = G t)
    {X A : ℕ → ι → Ω → ℝ} {Y Q : ι → Ω → ℝ}
    (hX : ∀ n t, MemLp (X n t) 2 P)
    (_hA : ∀ n t, Integrable (A n t) P)
    (hcomp : ∀ n, Martingale (fun t ω => X n t ω ^ 2 - A n t ω) (F n) P)
    (hY : StronglyAdapted G Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hQ : StronglyAdapted G Q) (hQint : ∀ t, Integrable (Q t) P)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 2 P) atTop (𝓝 0))
    (hAlim : ∀ t, Tendsto (fun n => eLpNorm (A n t - Q t) 1 P) atTop (𝓝 0)) :
    Martingale (fun t ω => Y t ω ^ 2 - Q t ω) G P := by
  apply martingale_of_growing_filtration_L1_limits F G hmono hsup hcomp
  · exact fun t => ((hY t).pow 2).sub (hQ t)
  · exact fun t => (hY2 t).integrable_sq.sub (hQint t)
  · intro t
    have hs := CompensatedSquareLimit.tendsto_eLpNorm_sq_sub
      (fun n => (hX n t).aestronglyMeasurable) (hY2 t) (hlim t)
    have hb := hs.add (hAlim t)
    simp only [add_zero] at hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    intro n
    have heq : (fun ω => X n t ω ^ 2 - A n t ω) -
        (fun ω => Y t ω ^ 2 - Q t ω) =
        (fun ω => X n t ω ^ 2 - Y t ω ^ 2) - (A n t - Q t) := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le le_rfl

end Problem367.GrowingFiltrationMartingale

end

end OAI
