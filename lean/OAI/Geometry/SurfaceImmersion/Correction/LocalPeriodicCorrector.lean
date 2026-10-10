import OAI.Geometry.SurfaceImmersion.Geometry.LocalIntegratedCovariance
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicCalculus
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCorrector
import OAI.Geometry.SurfaceImmersion.Correction.PeriodicCorrectorFormula

namespace OAI

/-! The explicit angular corrector over its open domain of admissibility. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma contDiffOn_spanSolve {O : Set A} {Y C : A → E} {a : A → ℝ × ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (ha : ContDiffOn ℝ ∞ a O) (hD : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => spanSolve (Y p) (C p) (a p)) O := by
  have hd : ContDiffOn ℝ ∞ (fun p => gramDet (Y p) (C p)) O :=
    ((hY.inner ℝ hY).mul (hC.inner ℝ hC)).sub ((hY.inner ℝ hC).pow 2)
  change ContDiffOn ℝ ∞ (fun p =>
    ((inner ℝ (C p) (C p) * (a p).1 - inner ℝ (Y p) (C p) * (a p).2) /
      gramDet (Y p) (C p)) • Y p +
    ((inner ℝ (Y p) (Y p) * (a p).2 - inner ℝ (Y p) (C p) * (a p).1) /
      gramDet (Y p) (C p)) • C p) O
  exact ((((hC.inner ℝ hC).mul ha.fst).sub ((hY.inner ℝ hC).mul ha.snd)).div hd hD).smul hY |>.add
    (((((hY.inner ℝ hY).mul ha.snd).sub ((hY.inner ℝ hC).mul ha.fst)).div hd hD).smul hC)

/-- A smooth family of solutions of the angular equations, with zero mean.
The varying subspace is used only for orthogonality and membership; the
actual covariance solve takes place in the fixed ambient Euclidean space. -/
theorem solve_smooth_family_on_formula (O : Set A) (hO : IsOpen O) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h K e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hKs : ContDiffOn ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmK : ∀ p ∈ O, average (K p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period)) (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (C p) (U p t) = K p t ∧ inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p) (U p (t : Period)) =
        PeriodicPrimitive.primitive (fun s : ℝ => h p (s : Period)) t) ∧
      (∀ p ∈ O, h p = 0 → K p = 0 → e p = 0 → U p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U p (t : Period) =
        JetPolynomial.angularCorrectionFunction (Y p) (C p) (X₀ p) (V p) (q p)
          (fun s => h p (s : Period)) (fun s => K p (s : Period))
          (fun s => e p (s : Period)) t) := by
  let H : A → C(Period, ℝ) := primitiveOn h O hO hhs hmh
  let K' : A → C(Period, ℝ) := angleOn K O hO hKs
  have hHs : ContDiffOn ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth h O hO hhs hmh
  have hK's : ContDiffOn ℝ ∞ (fun z : A × ℝ => K' z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    angleOn_smooth K O hO hKs
  let T : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (H p t, K p t),
      (spanSolve (Y p) (C p)).continuous.comp ((H p).continuous.prodMk (K p).continuous)⟩
  let T' : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (h p t, K' p t),
      (spanSolve (Y p) (C p)).continuous.comp ((h p).continuous.prodMk (K' p).continuous)⟩
  have hTs : ContDiffOn ℝ ∞ (fun z : A × ℝ => T z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_spanSolve (hY.comp contDiffOn_fst (fun _ hz => hz.1))
      (hC.comp contDiffOn_fst (fun _ hz => hz.1))
      (hHs.prodMk hKs) (fun z hz => hdet z.1 hz.1)
  have hT's : ContDiffOn ℝ ∞ (fun z : A × ℝ => T' z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_spanSolve (hY.comp contDiffOn_fst (fun _ hz => hz.1))
      (hC.comp contDiffOn_fst (fun _ hz => hz.1))
      (hhs.prodMk hK's) (fun z hz => hdet z.1 hz.1)
  have hTd (p : A) (hp : p ∈ O) (t : ℝ) : HasDerivAt (fun s : ℝ => T p (s : Period)) (T' p (t : Period)) t :=
    (spanSolve (Y p) (C p)).hasFDerivAt.comp_hasDerivAt t
      ((primitiveOn_hasDerivAt h O hO hhs hmh hp t).prodMk (angleOn_hasDerivAt K O hO hKs hp t))
  let X : A → C(Period, E) := fun p => ContinuousMap.const Period (X₀ p) + V p
  have hXs : ContDiffOn ℝ ∞ (fun z : A × ℝ => X z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    (hX₀.comp contDiffOn_fst (fun _ hz => hz.1)).add hV
  let a : A → C(Period, ℝ) := fun p =>
    ⟨fun t => inner ℝ (X p t) (T' p t), (X p).continuous.inner (T' p).continuous⟩
  have has : ContDiffOn ℝ ∞ (fun z : A × ℝ => a z.1 (z.2 : Period)) (O ×ˢ Set.univ) := hXs.inner ℝ hT's
  let r : A → C(Period, ℝ) := fun p => e p - (a p - ContinuousMap.const Period (average (a p)))
  have hrs : ContDiffOn ℝ ∞ (fun z : A × ℝ => r z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    hes.sub (has.sub ((contDiffOn_average_joint hO has).comp contDiffOn_fst (fun _ hz => hz.1)))
  have hr0 (p : A) (hp : p ∈ O) : average (r p) = 0 := by
    change average (fun t => e p t - fluctuation (a p) t) = 0
    rw [average_sub (f := e p) (g := fluctuation (a p)) (e p).continuous
      ((a p).continuous.sub continuous_const), hme p hp, average_fluctuation (a p).continuous, sub_self]
  let W : A → C(Period, E) := correctorFamily V r q
  have hWs : ContDiffOn ℝ ∞ (fun z : A × ℝ => W z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_parameterCorrector_joint hO hV hrs hq hqpos hcircle
  have hW0 (p : A) (hp : p ∈ O) : average (W p) = 0 := parameterCorrector_average_at p (hqpos p hp) (hcircle p hp)
  let Z : A → C(Period, E) := primitiveOn W O hO hWs hW0
  have hZs : ContDiffOn ℝ ∞ (fun z : A × ℝ => Z z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth W O hO hWs hW0
  have hWmem (p : A) (hp : p ∈ O) (t : Period) : W p t ∈ S p :=
    parameterCorrector_mem_submodule_at (S p) V r q p (hVmem p hp) (hqpos p hp) (hcircle p hp) t
  have hZmem (p : A) (hp : p ∈ O) (t : Period) : Z p t ∈ S p := by
    refine Quotient.inductionOn' t ?_
    intro x
    rw [primitiveOn_apply W O hO hWs hW0 hp]
    exact PeriodicPrimitive.primitive_mem_submodule (S p)
      ((W p).continuous.comp (AddCircle.continuous_mk' 1)) (fun s => hWmem p hp (s : Period)) x
  let U : A → C(Period, E) := fun p => T p + Z p
  let D : A → C(Period, E) := fun p => T' p + W p
  have hU0 (p : A) (hp : p ∈ O) : average (U p) = 0 := by
    change average (fun t => T p t + Z p t) = 0
    rw [average_add (f := T p) (g := Z p) (T p).continuous (Z p).continuous]
    have ht0 := average_spanSolve (Y p) (C p) (H p).continuous (K p).continuous
      (primitiveOn_mean_zero h O hO hhs hmh hp) (hmK p hp)
    change average (T p) = 0 at ht0
    rw [ht0, zero_add]
    exact primitiveOn_mean_zero W O hO hWs hW0 hp
  refine ⟨U, D, hTs.add hZs, hT's.add hWs, hU0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp t
    exact (hTd p hp t).add (primitiveOn_hasDerivAt W O hO hWs hW0 hp t)
  · intro p hp t
    have hy := hPY p hp (W p t) (hWmem p hp t)
    have hc := hPC p hp (Z p t) (hZmem p hp t)
    change inner ℝ (C p) (T p t + Z p t) = _ ∧ inner ℝ (Y p) (T' p t + W p t) = _
    rw [inner_add_right, hc, add_zero, inner_add_right, hy, add_zero]
    exact ⟨(spanSolve_pairings (Y p) (C p) (hdet p hp) _).2,
      (spanSolve_pairings (Y p) (C p) (hdet p hp) _).1⟩
  · intro p hp
    have hs := parameterCorrector_projection_at p (hr0 p hp) (hqpos p hp) (hcircle p hp)
    have heq : (fun t => inner ℝ (X₀ p + V p t) (D p t)) =
        (fun t => a p t + inner ℝ (V p t) (W p t)) := by
      funext t
      change inner ℝ (X₀ p + V p t) (T' p t + W p t) =
        inner ℝ (X₀ p + V p t) (T' p t) + inner ℝ (V p t) (W p t)
      simp only [inner_add_right, inner_add_left, hPX p hp _ (hWmem p hp t), zero_add]
    rw [heq]
    change (fun t => a p t + inner ℝ (V p t) (W p t) -
      average (fun s => a p s + inner ℝ (V p s) (W p s))) = e p
    rw [average_add (a p).continuous ((V p).continuous.inner (W p).continuous)]
    funext t
    have ht := congrFun hs t
    change inner ℝ (V p t) (W p t) - average (fun s => inner ℝ (V p s) (W p s)) =
      e p t - (a p t - average (a p)) at ht
    linarith
  · intro p hp t
    change inner ℝ (Y p) (T p (t : Period) + Z p (t : Period)) = _
    rw [inner_add_right, hPY p hp _ (hZmem p hp (t : Period)), add_zero]
    exact (spanSolve_pairings (Y p) (C p) (hdet p hp) (H p (t : Period), K p (t : Period))).1.trans
      (primitiveOn_apply h O hO hhs hmh hp t)
  · intro p hp hh hK he
    have hHp : H p = 0 := primitiveOn_zero_at h O hO hhs hmh hp hh
    have hK'p : K' p = 0 := angleOn_zero_at K O hO hKs hp hK
    have hTp : T p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (H p t, K p t) = 0
      rw [hHp, hK]
      exact (spanSolve (Y p) (C p)).map_zero
    have hT'p : T' p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (h p t, K' p t) = 0
      rw [hh, hK'p]
      exact (spanSolve (Y p) (C p)).map_zero
    have hap : a p = 0 := by
      ext t
      change inner ℝ (X p t) (T' p t) = 0
      rw [hT'p]
      exact inner_zero_right _
    have hrp : r p = 0 := by
      ext t
      change e p t - (a p t - average (a p)) = 0
      rw [he, hap]
      change (0 : ℝ) - (0 - average (fun _ => (0 : ℝ))) = 0
      rw [average_const, sub_self, sub_self]
    have hWp : W p = 0 := by
      ext t
      exact parameterCorrector_zero (fun s => congrArg (fun f : C(Period, ℝ) => f s) hrp) t
    have hZp : Z p = 0 := primitiveOn_zero_at W O hO hWs hW0 hp hWp
    change T p + Z p = 0
    rw [hTp, hZp, add_zero]

  · intro p hp t
    have hk (s : ℝ) : K' p (s : Period) = deriv (fun u : ℝ => K p (u : Period)) s :=
      (angleOn_hasDerivAt K O hO hKs hp s).deriv.symm
    have hr (s : ℝ) : r p (s : Period) =
        JetPolynomial.angularSourceFunction (Y p) (C p) (X₀ p) (V p)
          (fun u => h p (u : Period)) (fun u => K p (u : Period))
          (fun u => e p (u : Period)) s := by
      have havg : average (a p) = ∫ u in 0..1, a p (u : Period) :=
        (PeriodicPrimitive.integral_lift_eq_haar (a p)).symm
      change e p (s : Period) - (a p (s : Period) - average (a p)) = _
      rw [havg]
      change e p (s : Period) -
        (inner ℝ (X₀ p + V p (s : Period))
          (spanSolve (Y p) (C p) (h p (s : Period), K' p (s : Period))) -
          ∫ u in 0..1, inner ℝ (X₀ p + V p (u : Period))
            (spanSolve (Y p) (C p) (h p (u : Period), K' p (u : Period)))) = _
      simp only [JetPolynomial.angularSourceFunction, hk]
    change T p (t : Period) + Z p (t : Period) = _
    rw [primitiveOn_apply W O hO hWs hW0 hp]
    change spanSolve (Y p) (C p) (H p (t : Period), K p (t : Period)) + _ = _
    rw [primitiveOn_apply h O hO hhs hmh hp]
    unfold JetPolynomial.angularCorrectionFunction
    congr 1
    congr 1
    funext s
    change parameterCorrector V r q p (s : Period) = _
    rw [← realCorrector_eq_parameterCorrector V q r p s]
    congr 1
    exact funext hr

theorem solve_smooth_family_on (O : Set A) (hO : IsOpen O) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h K e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hKs : ContDiffOn ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmK : ∀ p ∈ O, average (K p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period)) (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (C p) (U p t) = K p t ∧ inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p) (U p (t : Period)) =
        PeriodicPrimitive.primitive (fun s : ℝ => h p (s : Period)) t) ∧
      (∀ p ∈ O, h p = 0 → K p = 0 → e p = 0 → U p = 0) := by
  obtain ⟨U, D, hUs, hDs, hU0, hUd, hp, hf, hH, hz, _⟩ :=
    solve_smooth_family_on_formula O hO S Y C X₀ hY hC hX₀ hdet hPY hPC hPX V hVmem hV q hq hqpos hcircle h K e hhs hKs hes hmh hmK hme
  exact ⟨U, D, hUs, hDs, hU0, hUd, hp, hf, hH, hz⟩

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
