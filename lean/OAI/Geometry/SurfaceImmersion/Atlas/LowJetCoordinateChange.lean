import OAI.Geometry.SurfaceImmersion.Geometry.LowJetChainRule

namespace OAI

/-! Exact order-two jet transport under a fixed smooth coordinate map.
The new position is supplied separately, so no inverse coordinate map is
required and the construction applies to arbitrary smooth maps. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology

namespace ClosedSurfaceR4.JetPolynomial

/-- One fixed coordinate derivative of a scalar function. -/
def coordinatePartial (f : Base → ℝ) (v : Fin 2) : Base → ℝ :=
  fun x => fderiv ℝ f x (coordinateVector v)

lemma coordinatePartial_smooth {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Fin 2) :
    ContDiff ℝ ∞ (coordinatePartial f v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private lemma coordinateVector_expansion (v : Base) :
    v = ∑ i : Fin 2, v i • coordinateVector i := by
  ext i
  simp [coordinateVector,Pi.single_apply]

private lemma coordinatePartial_component {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v i : Fin 2) (x : Base) :
    coordinatePartial (fun y => T y i) v x = (fderiv ℝ T x (coordinateVector v)) i := by
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply (hT.differentiable (by simp) x) i)
  simpa only [coordinatePartial,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using h

lemma coordinatePartial_comp {f : Base → ℝ} {T : Base → Base}
    (hf : ContDiff ℝ ∞ f) (hT : ContDiff ℝ ∞ T) (v : Fin 2) (x : Base) :
    coordinatePartial (f ∘ T) v x =
      ∑ i : Fin 2, coordinatePartial (fun y => T y i) v x * coordinatePartial f i (T x) := by
  change fderiv ℝ (f ∘ T) x (coordinateVector v) = _
  rw [fderiv_comp x (hf.differentiable (by simp) _) (hT.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; rw [coordinateVector_expansion (fderiv ℝ T x (coordinateVector v))]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinatePartial_component hT]
  rfl

lemma coordinatePartial_coordinatePartial_comp {f : Base → ℝ} {T : Base → Base}
    (hf : ContDiff ℝ ∞ f) (hT : ContDiff ℝ ∞ T) (v w : Fin 2) (x : Base) :
    coordinatePartial (coordinatePartial (f ∘ T) w) v x =
      ∑ i : Fin 2,
        (coordinatePartial (fun y => T y i) w x *
          (∑ j : Fin 2, coordinatePartial (fun y => T y j) v x *
            coordinatePartial (coordinatePartial f i) j (T x)) +
        coordinatePartial (coordinatePartial (fun y => T y i) w) v x *
          coordinatePartial f i (T x)) := by
  have he : coordinatePartial (f ∘ T) w = fun y =>
      ∑ i : Fin 2, coordinatePartial (fun z => T z i) w y * coordinatePartial f i (T y) :=
    funext (coordinatePartial_comp hf hT w)
  have hTi (i : Fin 2) : ContDiff ℝ ∞ (coordinatePartial (fun y => T y i) w) :=
    coordinatePartial_smooth (contDiff_pi.mp hT i) w
  have hfi (i : Fin 2) : ContDiff ℝ ∞ (fun y => coordinatePartial f i (T y)) :=
    (coordinatePartial_smooth hf i).comp hT
  change fderiv ℝ (coordinatePartial (f ∘ T) w) x (coordinateVector v) = _
  rw [he,fderiv_fun_sum (fun i _ => ((hTi i).mul (hfi i)).differentiable (by simp) x)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul ((hTi i).differentiable (by simp) x) ((hfi i).differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change coordinatePartial (fun y => T y i) w x *
      coordinatePartial (coordinatePartial f i ∘ T) v x +
      coordinatePartial f i (T x) *
        coordinatePartial (coordinatePartial (fun y => T y i) w) v x = _
  rw [coordinatePartial_comp (coordinatePartial_smooth hf i) hT]
  ring

/-- Slots of the two first and four ordered second coordinate derivatives. -/
def firstJetSlot : Fin 2 → Fin 7 := ![1,2]
def secondJetSlot : Fin 2 → Fin 2 → Fin 7 := ![![3,4],![5,6]]

lemma lowJet_first_slot (G : Base → Space) (v : Fin 2) (a : Fin 4) (x : Base) :
    lowJet G x (.inr (firstJetSlot v,a)) = coordinatePartial (fun y => G y a) v x := by
  fin_cases v <;> rfl

lemma lowJet_second_slot (G : Base → Space) (v w : Fin 2) (a : Fin 4) (x : Base) :
    lowJet G x (.inr (secondJetSlot v w,a)) =
      coordinatePartial (coordinatePartial (fun y => G y a) w) v x := by
  fin_cases v <;> fin_cases w <;> rfl

/-- First derivative of the composed map, linear in the supplied jet. -/
def coordinateChangeFirst (T : Base → Base) (x : Base) (J : LowJet)
    (v : Fin 2) (a : Fin 4) : ℝ :=
  ∑ i : Fin 2, coordinatePartial (fun y => T y i) v x * J (.inr (firstJetSlot i,a))

/-- Ordered second derivative, with both the Hessian and acceleration terms. -/
def coordinateChangeSecond (T : Base → Base) (x : Base) (J : LowJet)
    (v w : Fin 2) (a : Fin 4) : ℝ :=
  ∑ i : Fin 2,
    (coordinatePartial (fun y => T y i) w x *
      (∑ j : Fin 2, coordinatePartial (fun y => T y j) v x * J (.inr (secondJetSlot j i,a))) +
    coordinatePartial (coordinatePartial (fun y => T y i) w) v x * J (.inr (firstJetSlot i,a)))

/-- Transport a positional low jet at `T x` to the positional low jet at `x`.
The old positional components are unnecessary; the value and ordered jets
are evaluated by the chain rule. -/
def lowJetCoordinateChange (T : Base → Base) (p : Base × LowJet) : LowJet
  | .inl i => p.1 i
  | .inr (w,a) => ![p.2 (.inr (0,a)),
      coordinateChangeFirst T p.1 p.2 0 a,
      coordinateChangeFirst T p.1 p.2 1 a,
      coordinateChangeSecond T p.1 p.2 0 0 a,
      coordinateChangeSecond T p.1 p.2 0 1 a,
      coordinateChangeSecond T p.1 p.2 1 0 a,
      coordinateChangeSecond T p.1 p.2 1 1 a] w

lemma coordinateChangeFirst_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeFirst T p.1 p.2 v a) := by
  apply ContDiff.sum
  intro i _
  exact ((coordinatePartial_smooth (contDiff_pi.mp hT i) v).comp contDiff_fst).mul
    ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma coordinateChangeSecond_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v w : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeSecond T p.1 p.2 v w a) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.add
  · apply ContDiff.mul
    · exact (coordinatePartial_smooth (contDiff_pi.mp hT i) w).comp contDiff_fst
    · apply ContDiff.sum
      intro j _
      exact ((coordinatePartial_smooth (contDiff_pi.mp hT j) v).comp contDiff_fst).mul
        ((ContinuousLinearMap.proj (.inr (secondJetSlot j i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
          contDiff_snd)
  · exact ((coordinatePartial_smooth
      (coordinatePartial_smooth (contDiff_pi.mp hT i) w) v).comp contDiff_fst).mul
      ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma lowJetCoordinateChange_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (lowJetCoordinateChange T) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i =>
    exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))
  | inr i =>
    rcases i with ⟨w,a⟩
    fin_cases w
    · exact (ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
        (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Base × LowJet → LowJet))
    · exact coordinateChangeFirst_smooth hT 0 a
    · exact coordinateChangeFirst_smooth hT 1 a
    · exact coordinateChangeSecond_smooth hT 0 0 a
    · exact coordinateChangeSecond_smooth hT 0 1 a
    · exact coordinateChangeSecond_smooth hT 1 0 a
    · exact coordinateChangeSecond_smooth hT 1 1 a

/-- The finite-dimensional transport agrees exactly with the low jet of
the composed smooth map. -/
theorem lowJetCoordinateChange_eval {G : Base → Space} {T : Base → Base}
    (hG : ContDiff ℝ ∞ G) (hT : ContDiff ℝ ∞ T) (x : Base) :
    lowJetCoordinateChange T (x,lowJet G (T x)) = lowJet (G ∘ T) x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    rcases i with ⟨w,a⟩
    have hfirst (v : Fin 2) : coordinateChangeFirst T x (lowJet G (T x)) v a =
        coordinatePartial ((fun y => G y a) ∘ T) v x := by
      rw [coordinatePartial_comp (contDiff_pi.mp hG a) hT]
      simp only [coordinateChangeFirst,lowJet_first_slot]
    have hsecond (v w : Fin 2) : coordinateChangeSecond T x (lowJet G (T x)) v w a =
        coordinatePartial (coordinatePartial ((fun y => G y a) ∘ T) w) v x := by
      rw [coordinatePartial_coordinatePartial_comp (contDiff_pi.mp hG a) hT]
      simp only [coordinateChangeSecond,lowJet_first_slot,lowJet_second_slot]
    fin_cases w
    · rfl
    · exact hfirst 0
    · exact hfirst 1
    · exact hsecond 0 0
    · exact hsecond 0 1
    · exact hsecond 1 0
    · exact hsecond 1 1


private lemma iteratedDirectional_eventuallyEq {f g : Base → ℝ} {x : Base}
    (h : f =ᶠ[𝓝 x] g) (vs : List Base) :
    WeightedEstimates.iteratedDirectional vs f =ᶠ[𝓝 x]
      WeightedEstimates.iteratedDirectional vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Base →L[ℝ] ℝ => L v) hy

/-- Positional jets only depend on the germ of the map. -/
lemma lowJet_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) : lowJet G x = lowJet H x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have ha : (fun y => G y i.2) =ᶠ[𝓝 x] (fun y => H y i.2) :=
      h.mono (fun _ he => congrFun he i.2)
    exact (iteratedDirectional_eventuallyEq ha ((lowWord i.1).map coordinateVector)).self_of_nhds

/-- Evaluate the inverse-coordinate transport at `T x`. The only map
identification required here is the actual local germ `H ∘ S = G`. -/
lemma lowJetCoordinateChange_inverse_eval {G H : Base → Space} {T S : Base → Base}
    (hH : ContDiff ℝ ∞ H) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hrel : (H ∘ S) =ᶠ[𝓝 (T x)] G) :
    lowJetCoordinateChange S (T x,lowJet H x) = lowJet G (T x) := by
  have h := lowJetCoordinateChange_eval hH hS (T x)
  rw [hST] at h
  exact h.trans (lowJet_eventuallyEq hrel)

/-- A local inverse and the local relation `H = G ∘ T` supply the germ in
`lowJetCoordinateChange_inverse_eval`. -/
lemma lowJetCoordinateChange_local_inverse {G H : Base → Space} {T S : Base → Base}
    (hH : ContDiff ℝ ∞ H) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hTS : (T ∘ S) =ᶠ[𝓝 (T x)] id)
    (hrel : H =ᶠ[𝓝 x] (G ∘ T)) :
    lowJetCoordinateChange S (T x,lowJet H x) = lowJet G (T x) := by
  apply lowJetCoordinateChange_inverse_eval hH hS x hST
  have ht : Filter.Tendsto S (𝓝 (T x)) (𝓝 x) := by
    have hc : ContinuousAt S (T x) := hS.continuous.continuousAt
    change Filter.Tendsto S (𝓝 (T x)) (𝓝 (S (T x))) at hc
    rw [hST] at hc
    exact hc
  filter_upwards [hrel.comp_tendsto ht,hTS] with y hy hz
  change H (S y) = G y
  change H (S y) = G (T (S y)) at hy
  change T (S y) = y at hz
  simpa only [hz] using hy

end ClosedSurfaceR4.JetPolynomial

end

end OAI
