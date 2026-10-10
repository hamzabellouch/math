import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.IndependentProcessVectors

variable {Ω I J T E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem iIndepFun_curry {X : I → J → Ω → E}
    (hX : ∀ i j, Measurable (X i j))
    (h : iIndepFun (fun p : I × J => X p.1 p.2) P) :
    iIndepFun (fun i ω j => X i j ω) P := by
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    inferInstance
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  have hflat : Measurable (fun ω (p : I × J) => X p.1 p.2 ω) := by fun_prop
  have hc : (fun ω i j => X i j ω) =
      (MeasurableEquiv.curry I J E) ∘ (fun ω (p : I × J) => X p.1 p.2 ω) := rfl
  rw [hc, ← Measure.map_map (MeasurableEquiv.curry I J E).measurable hflat,
    (iIndepFun.map_fun_eq_infinitePi_map (X := fun p : I × J => X p.1 p.2) (fun p => hX p.1 p.2) h), Measure.infinitePi_map_curry (fun i j => P.map (X i j))]
  congr 1
  funext i
  exact (iIndepFun.map_fun_eq_infinitePi_map (X := X i) (hX i)
    (h.precomp (g := fun j : J => (i, j)) (fun a b hab => (Prod.mk.inj hab).2))).symm

theorem hasIndepIncrements_vector [Preorder T]
    {B : I → T → Ω → ℝ}
    (hm : ∀ i t, Measurable (B i t))
    (hi : iIndepFun (fun i ω t => B i t ω) P)
    (hB : ∀ i, HasIndepIncrements (B i) P) (S : Finset I) :
    HasIndepIncrements
      (fun t ω => (WithLp.toLp 2 (fun i : S => B i t ω) : EuclideanSpace ℝ S)) P := by
  intro n times htimes
  let D (i : S) (j : Fin n) (ω : Ω) :=
    B i (times j.succ) ω - B i (times j.castSucc) ω
  have hD (i : S) (j : Fin n) : Measurable (D i j) := (hm _ _).sub (hm _ _)
  have hrows : iIndepFun (fun i : S => fun ω (j : Fin n) => D i j ω) P := by
    exact (hi.precomp Subtype.val_injective).comp
      (fun _ (z : T → ℝ) (j : Fin n) => z (times j.succ) - z (times j.castSucc))
      (by intro i; fun_prop)
  have hflat : iIndepFun (fun p : S × Fin n => D p.1 p.2) P :=
    iIndepFun_uncurry' hD hrows (fun i => hB i n times htimes)
  have hswap : iIndepFun (fun p : Fin n × S => D p.2 p.1) P :=
    hflat.precomp (Equiv.prodComm (Fin n) S).injective
  have hcols := iIndepFun_curry (fun j i => hD i j) hswap
  exact hcols.comp (fun _ => (MeasurableEquiv.toLp 2 (S → ℝ)))
    (fun _ => (MeasurableEquiv.toLp 2 (S → ℝ)).measurable)

omit [IsProbabilityMeasure P] in

theorem brownian_vector_increment_hasLaw
    {B : I → ℝ≥0 → Ω → ℝ}
    (hm : ∀ i t, Measurable (B i t))
    (hi : iIndepFun (fun i ω t => B i t ω) P)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : Finset I) (s t : ℝ≥0) :
    HasLaw (fun ω => (WithLp.toLp 2
      (fun i : S => B i t ω - B i s ω) : EuclideanSpace ℝ S))
      ((Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))).map
        (MeasurableEquiv.toLp 2 (S → ℝ))) P := by
  have hd : iIndepFun (fun i : S => fun ω => B i t ω - B i s ω) P :=
    (hi.precomp Subtype.val_injective).comp (fun _ (z : ℝ≥0 → ℝ) => z t - z s)
      (by intro i; fun_prop)
  have hl := hd.hasLaw_infinitePi (fun i : S => (hB i).hasLaw_sub t s)
    (Measurable.aemeasurable (by fun_prop))
  have he : HasLaw (MeasurableEquiv.toLp 2 (S → ℝ))
      ((Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))).map
        (MeasurableEquiv.toLp 2 (S → ℝ)))
      (Measure.infinitePi (fun _ : S => gaussianReal 0 (nndist t.1 s.1))) :=
    ⟨(MeasurableEquiv.toLp 2 (S → ℝ)).measurable.aemeasurable, rfl⟩
  exact he.comp hl

end Problem336.IndependentProcessVectors

end

end OAI
