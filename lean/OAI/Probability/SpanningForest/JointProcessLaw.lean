module

public import Mathlib
import all Mathlib.Probability.Independence.Process.HasIndepIncrements.IsGaussianProcess

namespace OAI

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem336.JointProcessLaw

variable {Ω Ω' T E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [LinearOrder T] [OrderBot T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {X : T → Ω → E} {Y : T → Ω' → E}

omit [IsProbabilityMeasure Q] in

theorem identDistrib_process_of_increments
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hX0 : ∀ᵐ ω ∂P, X ⊥ ω = 0) (hY0 : ∀ᵐ ω ∂Q, Y ⊥ ω = 0)
    (hXi : HasIndepIncrements X P) (hYi : HasIndepIncrements Y Q)
    (hinc : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => X t ω - X s ω) (fun ω => Y t ω - Y s ω) P Q) :
    IdentDistrib (fun ω t => X t ω) (fun ω t => Y t ω) P Q := by
  classical
  have hXm : Measurable (fun ω t => X t ω) := Measurable.of_eval hX
  have hYm : Measurable (fun ω t => Y t ω) := Measurable.of_eval hY
  have hrestrict (S : Finset T) :
      IdentDistrib (fun ω => S.restrict (X · ω))
        (fun ω => S.restrict (Y · ω)) P Q := by
    let DX : Fin S.card → Ω → E := fun i ω =>
      X (S.orderEmbOfFinWithBot i.succ) ω - X (S.orderEmbOfFinWithBot i.castSucc) ω
    let DY : Fin S.card → Ω' → E := fun i ω =>
      Y (S.orderEmbOfFinWithBot i.succ) ω - Y (S.orderEmbOfFinWithBot i.castSucc) ω
    have hDX : ∀ i, Measurable (DX i) := fun _ => (hX _).sub (hX _)
    have hDY : ∀ i, Measurable (DY i) := fun _ => (hY _).sub (hY _)
    have hdmap : P.map (fun ω i => DX i ω) = Q.map (fun ω i => DY i ω) := by
      rw [(hXi _ _ (S.monotone_orderEmbOfFinWithBot)).map_fun_eq_infinitePi_map hDX,
        (hYi _ _ (S.monotone_orderEmbOfFinWithBot)).map_fun_eq_infinitePi_map hDY]
      congr 1
      funext i
      exact (hinc _ _ (S.monotone_orderEmbOfFinWithBot (Fin.castSucc_le_succ i))).map_eq
    have hd : IdentDistrib (fun ω i => DX i ω) (fun ω i => DY i ω) P Q :=
      ⟨(Measurable.of_eval hDX).aemeasurable,
        (Measurable.of_eval hDY).aemeasurable, hdmap⟩
    have hc := hd.comp (incrementsToRestrict ℝ S).measurable
    have hx := incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hX0 S
    have hy := incrementsToRestrict_increments_orderEmbOfFinWithBot_ae_eq_restrict ℝ hY0 S
    exact ((IdentDistrib.of_ae_eq
      (Measurable.of_eval (fun i => hX i.1)).aemeasurable hx).trans hc).trans
      (IdentDistrib.of_ae_eq
        (Measurable.of_eval (fun i => hY i.1)).aemeasurable hy).symm
  refine ⟨hXm.aemeasurable, hYm.aemeasurable, ?_⟩
  let F (S : Finset T) : Measure (S → E) :=
    (P.map (fun ω t => X t ω)).map S.restrict
  have hp : IsProjectiveLimit (P.map (fun ω t => X t ω)) F := fun _ => rfl
  have hq : IsProjectiveLimit (Q.map (fun ω t => Y t ω)) F := by
    intro S
    have hm : Measurable (fun z : T → E => S.restrict z) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.1)
    change (Q.map (fun ω t => Y t ω)).map S.restrict =
      (P.map (fun ω t => X t ω)).map S.restrict
    rw [Measure.map_map hm hYm, Measure.map_map hm hXm]
    exact (hrestrict S).map_eq.symm
  exact hp.unique hq

omit [IsProbabilityMeasure Q] in

theorem identDistrib_family_of_finite_increments {I : Type*}
    {W : I → T → Ω → ℝ} {B : I → T → Ω' → ℝ}
    (hW : ∀ i t, Measurable (W i t)) (hB : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i ⊥ ω = 0)
    (hB0 : ∀ i, ∀ᵐ ω ∂Q, B i ⊥ ω = 0)
    (hWi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) P)
    (hBi : ∀ S : Finset I, HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) Q)
    (hinc : ∀ (S : Finset I) (s t : T), s ≤ t →
      IdentDistrib
        (fun ω => (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S))
        (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω - B i s ω) : EuclideanSpace ℝ S)) P Q) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  classical
  have hWm : Measurable (fun ω i t => W i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hW i))
  have hBm : Measurable (fun ω i t => B i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval (hB i))
  have hrestrict (S : Finset I) :
      IdentDistrib (fun ω => S.restrict (fun i t => W i t ω))
        (fun ω => S.restrict (fun i t => B i t ω)) P Q := by
    have hWS (t : T) : Measurable
        (fun ω => (WithLp.toLp 2 (fun i : S => W i t ω) : EuclideanSpace ℝ S)) :=
      (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
        (Measurable.of_eval (fun i => hW i t))
    have hBS (t : T) : Measurable
        (fun ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) :=
      (MeasurableEquiv.toLp 2 (S → ℝ)).measurable.comp
        (Measurable.of_eval (fun i => hB i t))
    have hWS0 : ∀ᵐ ω ∂P,
        (WithLp.toLp 2 (fun i : S => W i ⊥ ω) : EuclideanSpace ℝ S) = 0 := by
      filter_upwards [ae_all_iff.mpr (fun i : S => hW0 i)] with ω hω
      ext i
      exact hω i
    have hBS0 : ∀ᵐ ω ∂Q,
        (WithLp.toLp 2 (fun i : S => B i ⊥ ω) : EuclideanSpace ℝ S) = 0 := by
      filter_upwards [ae_all_iff.mpr (fun i : S => hB0 i)] with ω hω
      ext i
      exact hω i
    have hproc := identDistrib_process_of_increments hWS hBS hWS0 hBS0 (hWi S) (hBi S)
      (fun s t hst => hinc S s t hst)
    have hswap : Measurable (fun z : T → EuclideanSpace ℝ S => fun i : S => fun t => z t i) := by
      fun_prop
    exact hproc.comp hswap
  refine ⟨hWm.aemeasurable, hBm.aemeasurable, ?_⟩
  let F (S : Finset I) : Measure (S → T → ℝ) :=
    (P.map (fun ω i t => W i t ω)).map S.restrict
  have hp : IsProjectiveLimit (P.map (fun ω i t => W i t ω)) F := fun _ => rfl
  have hq : IsProjectiveLimit (Q.map (fun ω i t => B i t ω)) F := by
    intro S
    have hm : Measurable (fun z : I → T → ℝ => S.restrict z) :=
      Measurable.of_eval (fun i => measurable_pi_apply i.1)
    change (Q.map (fun ω i t => B i t ω)).map S.restrict =
      (P.map (fun ω i t => W i t ω)).map S.restrict
    rw [Measure.map_map hm hBm, Measure.map_map hm hWm]
    exact (hrestrict S).map_eq.symm
  exact hp.unique hq

end Problem336.JointProcessLaw

end
end

end OAI
