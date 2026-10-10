import OAI.Probability.ClassicalON.ReindexIntegral

namespace OAI

universe uA uE uF uV uW

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {W : Type uW} {E : Type uE} {F : Type uF} {A : Type uA} [Fintype V] [Fintype W] [Fintype E] [Fintype F]

def arrowEquiv (e : E ≃ F) : (E → A) ≃ (F → A) where
  toFun η := fun f => η (e.symm f)
  invFun η := fun f => η (e f)
  left_inv η := by funext f; simp
  right_inv η := by funext f; simp

omit [Fintype V] [Fintype W] in
theorem freeSpinEnergy_edgeEquiv (n : ℕ) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin n) (s' : W → Spin n)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) :
    freeSpinEnergy n l' r' b' s'=freeSpinEnergy n l r b s := by
  unfold freeSpinEnergy
  rw [← ee.sum_comp]
  simp_rw [hb,hl,hr]

omit [Fintype V] [Fintype W] in
theorem spinBondWeight_edgeEquiv (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin 3) (s' : W → Spin 3)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) (η : F → Bool) :
    spinBondWeight l' r' b' s' η=spinBondWeight l r b s (fun e => η (ee e)) := by
  unfold spinBondWeight spinBondParameter
  rw [← ee.prod_comp]
  simp_rw [hb,hl,hr]

omit [Fintype V] [Fintype W] in
theorem sum_spinBondWeight_edgeEquiv (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (s : V → Spin 3) (s' : W → Spin 3)
    (hb : ∀ e,b' (ee e)=b e) (hl : ∀ e,s' (l' (ee e))=s (l e))
    (hr : ∀ e,s' (r' (ee e))=s (r e)) (f : (E → Bool) → ℝ) :
    (∑ η,spinBondWeight l' r' b' s' η*f (fun e => η (ee e)))=
      ∑ η,spinBondWeight l r b s η*f η := by
  simp_rw [spinBondWeight_edgeEquiv ee l r l' r' b b' s s' hb hl hr]
  exact (arrowEquiv (A := Bool) ee).symm.sum_comp (fun η => spinBondWeight l r b s η*f η)

theorem poleBondMean_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W) (b : E → ℝ) (b' : F → ℝ)
    (B : Set V) (B' : Set W) (hb : ∀ e,b' (ee e)=b e)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (hB : ∀ v,ev v∈B' ↔ v∈B) (f : (E → Bool) → ℝ) :
    poleBondMean l' r' b' B' (fun _ => true) (fun η => f (fun e => η (ee e)))=
      poleBondMean l r b B (fun _ => true) f := by
  unfold poleBondMean
  rw [poleSystem_reference,poleSystem_reference]
  have he (s : W → Spin 3) : freeSpinEnergy 3 l' r' b' s=
      freeSpinEnergy 3 l r b (fun v => s (ev v)) :=
    freeSpinEnergy_edgeEquiv 3 ee _ _ _ _ _ _ _ _ hb
      (fun e => congrArg s (hl e)) (fun e => congrArg s (hr e))
  have hs (s : W → Spin 3) := sum_spinBondWeight_edgeEquiv ee l r l' r' b b'
    (fun v => s (ev v)) s hb (fun e => congrArg s (hl e)) (fun e => congrArg s (hr e)) f
  simp_rw [he,hs]
  let μ (w : W) : Measure (Spin 3) := if w∈B' then Measure.dirac (poleSpin true) else sphereProbability 3
  have : ∀ w,IsProbabilityMeasure (μ w) := by intro w; dsimp [μ]; split <;> infer_instance
  change weightedMean (Measure.pi μ) _ _=_
  rw [weightedMean_pi_reindex ev μ (fun s => Real.exp (freeSpinEnergy 3 l r b s))
    (fun s => ∑ η,spinBondWeight l r b s η*f η)]
  have hμ : (fun v => μ (ev v))=(fun v => if v∈B then Measure.dirac (poleSpin true) else sphereProbability 3) := by
    funext v
    simp only [μ,hB]
  rw [hμ]
  rfl

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] in
theorem bondConnected_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (η : F → Bool) (x y : V) :
    bondConnected l' r' η (ev x) (ev y) ↔ bondConnected l r (fun e => η (ee e)) x y := by
  constructor
  · intro h s hs
    have ht : (fun w => s (ev.symm w))∈bondSubspace l' r' η := by
      intro f hf
      obtain ⟨e,rfl⟩ := ee.surjective f
      simpa only [hl,hr,Equiv.symm_apply_apply] using hs e hf
    simpa only [Equiv.symm_apply_apply] using h _ ht
  · intro h s hs
    apply h (fun v => s (ev v))
    intro e he
    simpa only [hl,hr] using hs (ee e) he

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] in
theorem bondCrossing_reindex (ev : V ≃ W) (ee : E ≃ F)
    (l r : E → V) (l' r' : F → W)
    (hl : ∀ e,l' (ee e)=ev (l e)) (hr : ∀ e,r' (ee e)=ev (r e))
    (I O : Set V) (I' O' : Set W) (hI : ∀ v,ev v∈I' ↔ v∈I)
    (hO : ∀ v,ev v∈O' ↔ v∈O) (η : F → Bool) :
    bondCrossing l' r' I' O' η ↔ bondCrossing l r I O (fun e => η (ee e)) := by
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩
    obtain ⟨x,rfl⟩ := ev.surjective x
    obtain ⟨y,rfl⟩ := ev.surjective y
    exact ⟨x,(hI x).mp hx,y,(hO y).mp hy,(bondConnected_reindex ev ee l r l' r' hl hr η x y).mp hxy⟩
  · rintro ⟨x,hx,y,hy,hxy⟩
    exact ⟨ev x,(hI x).mpr hx,ev y,(hO y).mpr hy,(bondConnected_reindex ev ee l r l' r' hl hr η x y).mpr hxy⟩

end ClassicalON

end

end OAI
