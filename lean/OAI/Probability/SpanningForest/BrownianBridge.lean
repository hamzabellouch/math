import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336.BrownianBridge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

def residual (B : ℝ≥0 → Ω → ℝ) (t s : ℝ≥0) (ω : Ω) : ℝ :=
  B s ω - (s : ℝ) / (t : ℝ) * B t ω

theorem indepFun_residual_endpoint (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (s : Set.Iic t) => residual B t s ω) (B t) P := by
  have hm s := hB.aemeasurable s
  have h : IndepFun (fun ω (s : Set.Iic t) => residual B t s ω)
      (fun ω (_ : Unit) => B t ω) P := by
    apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    · apply hB.isGaussianProcess.of_isGaussianProcess
      rintro (⟨s, hs⟩ | _)
      · exact ⟨{s, t},
          { toFun x := x ⟨s, by simp⟩ - (s : ℝ) / (t : ℝ) * x ⟨t, by simp⟩
            map_add' x y := by simp; ring
            map_smul' c x := by simp; ring }, by simp [residual]⟩
      · exact ⟨{t},
          { toFun x := x ⟨t, by simp⟩
            map_add' x y := by simp
            map_smul' c x := by simp }, by simp⟩
    · intro s
      exact (hm s).sub ((hm t).const_mul _)
    · intro _
      exact hm t
    · rintro ⟨s, hs⟩ _
      have := hB.isGaussianProcess.isProbabilityMeasure
      unfold residual
      rw [covariance_fun_sub_left, covariance_const_mul_left,
        hB.covariance_eval, hB.covariance_eval, min_self, min_eq_left hs]
      · have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
        field_simp
        ring
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.const_mul _
      · exact (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  exact h.comp measurable_id (measurable_pi_apply ())

theorem indepFun_regroup {A C D : Type*} [MeasurableSpace A]
    [MeasurableSpace C] [MeasurableSpace D] [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → C} {Z : Ω → D}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω => (Y ω, Z ω)) P)
    (hYZ : IndepFun Y Z P) :
    IndepFun Y (fun ω => (X ω, Z ω)) P := by
  let μX := P.map X
  let μY := P.map Y
  let μZ := P.map Z
  let swapFirst : A × (C × D) → C × (A × D) := fun q => (q.2.1, q.1, q.2.2)
  have hm : Measurable swapFirst := by fun_prop
  have hp : MeasurePreserving swapFirst (μX.prod (μY.prod μZ))
      (μY.prod (μX.prod μZ)) := by
    exact (measurePreserving_prodAssoc μY μX μZ).comp
      (((Measure.measurePreserving_swap (μ := μX) (ν := μY)).prod
        (MeasurePreserving.id μZ)).comp
          ((measurePreserving_prodAssoc μX μY μZ).symm MeasurableEquiv.prodAssoc))
  have hpair : P.map (fun ω => (Y ω, Z ω)) = μY.prod μZ :=
    hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable
  have hall : P.map (fun ω => (X ω, (Y ω, Z ω))) = μX.prod (μY.prod μZ) := by
    rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable
      (hY.prodMk hZ).aemeasurable, hpair]
  have hxz : IndepFun X Z P := hXYZ.comp measurable_id measurable_snd
  apply (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable
    (hX.prodMk hZ).aemeasurable).2
  rw [hxz.map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable]
  change P.map (swapFirst ∘ (fun ω => (X ω, (Y ω, Z ω)))) = _
  rw [← Measure.map_map hm (hX.prodMk (hY.prodMk hZ)), hall]
  exact hp.map_eq

omit [MeasurableSpace Ω] in

theorem residual_add_linear (X : Ω → ℝ) (t s : ℝ≥0) (ht : t ≠ 0) (ω : Ω) :
    residual (fun r ω => (r : ℝ) * X ω + B r ω) t s ω = residual B t s ω := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  unfold residual
  field_simp
  ring

theorem indepFun_residual_hidden_endpoint (hB : IsPreBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) {X : Ω → ℝ} (hXm : Measurable X)
    (hXB : IndepFun X (fun ω s => B s ω) P) (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (s : Set.Iic t) => residual B t s ω)
      (fun ω => (X ω, (t : ℝ) * X ω + B t ω)) P := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hpair : IndepFun X
      (fun ω => ((fun s : Set.Iic t => residual B t s ω), B t ω)) P := by
    exact hXB.comp measurable_id
      (show Measurable (fun f : ℝ≥0 → ℝ =>
        ((fun s : Set.Iic t => f s - (s : ℝ) / (t : ℝ) * f t), f t)) by fun_prop)
  have hm : Measurable (fun ω (s : Set.Iic t) => residual B t s ω) := by
    apply Measurable.of_eval
    intro s
    exact (hBm s).sub ((hBm t).const_mul _)
  have h := indepFun_regroup hXm hm (hBm t) hpair (indepFun_residual_endpoint hB t ht)
  exact h.comp measurable_id
    (show Measurable (fun q : ℝ × ℝ => (q.1, (t : ℝ) * q.1 + q.2)) by fun_prop)

omit [MeasurableSpace Ω] in

theorem history_comap_eq_endpoint_residual (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => Y s ω) inferInstance =
      MeasurableSpace.comap
        (fun ω => (Y t ω, fun s : Set.Iic t => residual Y t s ω)) inferInstance := by
  let H := fun ω (s : Set.Iic t) => Y s ω
  let F := fun ω => (Y t ω, fun s : Set.Iic t => residual Y t s ω)
  let decompose : (Set.Iic t → ℝ) → ℝ × (Set.Iic t → ℝ) :=
    fun f => (f ⟨t, by simp⟩, fun s => f s - (s : ℝ) / (t : ℝ) * f ⟨t, by simp⟩)
  let assemble : ℝ × (Set.Iic t → ℝ) → (Set.Iic t → ℝ) :=
    fun q s => q.2 s + (s : ℝ) / (t : ℝ) * q.1
  have hd : Measurable decompose := by fun_prop
  have ha : Measurable assemble := by fun_prop
  have hF : F = decompose ∘ H := rfl
  have hH : H = assemble ∘ F := by
    funext ω s
    simp [H, F, assemble, residual]
  change MeasurableSpace.comap H _ = MeasurableSpace.comap F _
  apply le_antisymm
  · rw [hH, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ha.comap_le
  · rw [hF, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hd.comap_le

theorem isGaussianProcess_independent_family {I T : Type*}
    {C : I → T → Ω → ℝ} (hC : ∀ i, IsGaussianProcess (C i) P)
    (hind : iIndepFun (fun i ω t => C i t ω) P) :
    IsGaussianProcess (fun p : I × T => C p.1 p.2) P := by
  classical
  constructor
  intro S
  let J := S.image Prod.fst
  let K := S.image Prod.snd
  have hG : ∀ i : J, HasGaussianLaw (fun ω (t : K) => C i t ω) P :=
    fun i => (hC i).hasGaussianLaw K
  have hI : iIndepFun (fun (i : J) ω (t : K) => C i t ω) P := by
    exact (hind.precomp Subtype.val_injective).comp
      (fun _ f (t : K) => f t) (fun _ => by fun_prop)
  let L : (J → K → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun x := fun p => x ⟨p.1.1, Finset.mem_image_of_mem _ p.2⟩
        ⟨p.1.2, Finset.mem_image_of_mem _ p.2⟩
      map_add' x y := by rfl
      map_smul' c x := by rfl }
  exact (hI.hasGaussianLaw hG).map L

omit [MeasurableSpace Ω] in

theorem observation_history_comap (X : Ω → ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    MeasurableSpace.comap
      (fun ω (s : Set.Iic t) => (s : ℝ) * X ω + B s ω) inferInstance =
      MeasurableSpace.comap (fun ω => (t : ℝ) * X ω + B t ω) inferInstance ⊔
        MeasurableSpace.comap (fun ω (s : Set.Iic t) => residual B t s ω) inferInstance := by
  rw [history_comap_eq_endpoint_residual (fun r ω => (r : ℝ) * X ω + B r ω) t]
  simp_rw [residual_add_linear X t _ ht]
  exact MeasurableSpace.comap_prodMk _ _

theorem indepFun_residual_family_endpoint {I : Type*}
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P) (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω)
      (fun ω i => C i t ω) P := by
  classical
  have hp := hind.isProbabilityMeasure
  have hg := isGaussianProcess_independent_family (fun i => (hC i).isGaussianProcess) hind
  have hLp i s := ((hC i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have hm i s := (hC i).aemeasurable s
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
  · apply hg.of_isGaussianProcess
    rintro (⟨i, s, hs⟩ | i)
    · exact ⟨{(i, s), (i, t)},
        { toFun x := x ⟨(i, s), by simp⟩ - (s : ℝ) / (t : ℝ) * x ⟨(i, t), by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }, by simp [residual]⟩
    · exact ⟨{(i, t)},
        { toFun x := x ⟨(i, t), by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
  · intro p
    exact (hm p.1 p.2).sub ((hm p.1 t).const_mul _)
  · intro i
    exact hm i t
  · rintro ⟨i, s, hs⟩ j
    unfold residual
    rw [covariance_fun_sub_left (hLp i s) ((hLp i t).const_mul _) (hLp j t),
      covariance_const_mul_left]
    by_cases hij : i = j
    · subst j
      rw [(hC i).covariance_eval, (hC i).covariance_eval, min_self, min_eq_left hs]
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
      field_simp
      ring
    · have hc (r : ℝ≥0) : cov[C i r, C j t; P] = 0 :=
        ((hind.indepFun hij).comp (measurable_pi_apply r)
          (measurable_pi_apply t)).covariance_eq_zero (hLp i r) (hLp j t)
      rw [hc s, hc t]
      ring

theorem indepFun_residual_family_hidden_endpoint {I A : Type*} [MeasurableSpace A]
    {C : I → ℝ≥0 → Ω → ℝ} (hC : ∀ i, IsPreBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω s => C i s ω) P)
    (hCm : ∀ i s, Measurable (C i s)) {X : Ω → A} (hXm : Measurable X)
    (D : A → I → ℝ) (hD : Measurable D)
    (hXC : IndepFun X (fun ω (p : I × ℝ≥0) => C p.1 p.2 ω) P)
    (t : ℝ≥0) (ht : t ≠ 0) :
    IndepFun (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω)
      (fun ω => (X ω, fun i => (t : ℝ) * D (X ω) i + C i t ω)) P := by
  have := hind.isProbabilityMeasure
  have hpair : IndepFun X
      (fun ω => ((fun p : I × Set.Iic t => residual (C p.1) t p.2 ω),
        fun i => C i t ω)) P := by
    exact hXC.comp measurable_id
      (show Measurable (fun f : I × ℝ≥0 → ℝ =>
        ((fun p : I × Set.Iic t => f (p.1, p.2) -
          (p.2 : ℝ) / (t : ℝ) * f (p.1, t)), fun i => f (i, t))) by fun_prop)
  have hm : Measurable (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω) := by
    apply Measurable.of_eval
    intro p
    exact (hCm p.1 p.2).sub ((hCm p.1 t).const_mul _)
  have hE : Measurable (fun ω i => C i t ω) := Measurable.of_eval (fun i => hCm i t)
  have h := indepFun_regroup hXm hm hE hpair (indepFun_residual_family_endpoint hC hind t ht)
  exact h.comp measurable_id
    (show Measurable (fun q : A × (I → ℝ) =>
      (q.1, fun i => (t : ℝ) * D q.1 i + q.2 i)) by fun_prop)

omit [MeasurableSpace Ω] in

theorem observation_family_history_comap {I A : Type*} (C : I → ℝ≥0 → Ω → ℝ)
    (X : Ω → A) (D : A → I → ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    MeasurableSpace.comap
      (fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω) inferInstance =
      MeasurableSpace.comap (fun ω i => (t : ℝ) * D (X ω) i + C i t ω) inferInstance ⊔
        MeasurableSpace.comap
          (fun ω (p : I × Set.Iic t) => residual (C p.1) t p.2 ω) inferInstance := by
  let H := fun ω (p : I × Set.Iic t) => (p.2 : ℝ) * D (X ω) p.1 + C p.1 p.2 ω
  let F := fun ω => ((fun i => (t : ℝ) * D (X ω) i + C i t ω),
    fun p : I × Set.Iic t => residual (C p.1) t p.2 ω)
  let decompose : (I × Set.Iic t → ℝ) → (I → ℝ) × (I × Set.Iic t → ℝ) :=
    fun f => (fun i => f (i, ⟨t, by simp⟩),
      fun p => f p - (p.2 : ℝ) / (t : ℝ) * f (p.1, ⟨t, by simp⟩))
  let assemble : (I → ℝ) × (I × Set.Iic t → ℝ) → (I × Set.Iic t → ℝ) :=
    fun q p => q.2 p + (p.2 : ℝ) / (t : ℝ) * q.1 p.1
  have hd : Measurable decompose := by fun_prop
  have ha : Measurable assemble := by fun_prop
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hF : F = decompose ∘ H := by
    funext ω
    apply Prod.ext
    · rfl
    · funext p
      dsimp [F, decompose, H, residual]
      field_simp
      ring
  have hH : H = assemble ∘ F := by
    funext ω p
    dsimp [H, F, assemble, residual]
    field_simp
    ring
  rw [← MeasurableSpace.comap_prodMk]
  change MeasurableSpace.comap H _ = MeasurableSpace.comap F _
  apply le_antisymm
  · rw [hH, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ha.comap_le
  · rw [hF, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hd.comap_le

end Problem336.BrownianBridge

end

end OAI
