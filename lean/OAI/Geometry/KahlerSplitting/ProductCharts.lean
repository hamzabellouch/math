import OAI.Geometry.KahlerSplitting.Frobenius

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_frobenius {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin s → ℂ)) E,
      (0 : (Fin r → ℂ) × (Fin s → ℂ)) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨L,hL⟩ := exists_projection_coordinates (P p) (hid p hp) hr hs
  let J : (Fin r → ℂ) →L[ℂ] ((Fin r → ℂ) × (Fin s → ℂ)) :=
    (ContinuousLinearMap.id ℂ (Fin r → ℂ)).prod 0
  let A : (Fin r → ℂ) →L[ℂ] E := L.toContinuousLinearMap.comp J
  let Q : E →L[ℂ] (Fin r → ℂ) :=
    (ContinuousLinearMap.fst ℂ (Fin r → ℂ) (Fin s → ℂ)).comp L.symm.toContinuousLinearMap
  have hQA : Q.comp A = ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
    ext t
    simp [Q,A,J]
  have hAQ : A.comp Q = P p := by
    apply ContinuousLinearMap.ext
    intro v
    exact hL v
  obtain ⟨O,hOo,hOp,hOU,W,V,D,hWp,hW,hV,hcomm⟩ :=
    exists_normalized_commuting_frame hU P hP hid hInt hp r A Q hQA hAQ
  obtain ⟨G⟩ := exists_commutingFlowData r V D hOo (fun i x hx ↦ (hV i x hx).2) hcomm hOp
  have hV0 (i : Fin r) : V i p = L (Pi.single i 1,0) := by
    rw [(hV i p hOp).1,hWp]
    rfl
  obtain ⟨e,he0,hep,heO,he,hei,hker⟩ := foliation_chart_from_flows G L hV0 P W Q
    (fun i x hx ↦ (hV i x hx).1) (fun x hx ↦ (hW x hx).1)
    (fun x hx ↦ (hW x hx).2.2)
  exact ⟨e,he0,hep,heO.trans hOU,he,hei,hker⟩

end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma projection_complement_idempotent (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) (v : E) :
    (ContinuousLinearMap.id ℂ E-P) ((ContinuousLinearMap.id ℂ E-P) v) =
      (ContinuousLinearMap.id ℂ E-P) v := by
  simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,hP,sub_self,sub_zero]

lemma projection_complement_range (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) :
    LinearMap.range (ContinuousLinearMap.id ℂ E-P).toLinearMap = LinearMap.ker P.toLinearMap := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change P (w-P w) = 0
    rw [map_sub,hP,sub_self]
  · intro hv
    refine ⟨v,?_⟩
    change v-P v = v
    rw [show P v = 0 from hv,sub_zero]

lemma projection_complement_ker (P : E →L[ℂ] E)
    (hP : ∀ v, P (P v) = P v) :
    LinearMap.ker (ContinuousLinearMap.id ℂ E-P).toLinearMap = LinearMap.range P.toLinearMap := by
  ext v
  constructor
  · intro hv
    refine ⟨v,?_⟩
    exact (sub_eq_zero.mp (show v-P v = 0 from hv)).symm
  · rintro ⟨w,rfl⟩
    change P w-P (P w) = 0
    rw [hP,sub_self]

lemma complement_fixed_iff_zero (P : E →L[ℂ] E) (v : E) :
    (ContinuousLinearMap.id ℂ E-P) v = v ↔ P v = 0 := by
  change v-P v = v ↔ P v = 0
  exact sub_eq_self

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E R S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]

theorem combine_foliation_charts (P : E → E →L[ℂ] E)
    (e₁ : OpenPartialHomeomorph (R × S) E) (e₂ : OpenPartialHomeomorph (S × R) E)
    (h₁ : ContDiffOn ℂ 1 e₁.symm e₁.target) (h₂ : ContDiffOn ℂ 1 e₂.symm e₂.target)
    (hk₁ : ∀ y ∈ e₁.target, ∀ v, P y v = v ↔ (fderiv ℂ e₁.symm y v).2 = 0)
    (hk₂ : ∀ y ∈ e₂.target, ∀ v, P y v = 0 ↔ (fderiv ℂ e₂.symm y v).2 = 0)
    {p : E} (hp₁ : p ∈ e₁.target) (hp₂ : p ∈ e₂.target)
    (h0₁ : e₁.symm p = 0) (h0₂ : e₂.symm p = 0)
    (L : (R × S) ≃L[ℂ] E) :
    ∃ e : OpenPartialHomeomorph E (R × S), p ∈ e.source ∧ e p = 0 ∧
      e.source ⊆ e₁.target ∩ e₂.target ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v,
        (P y v = v ↔ (fderiv ℂ e y v).2 = 0) ∧
        (P y v = 0 ↔ (fderiv ℂ e y v).1 = 0) := by
  let U := e₁.target ∩ e₂.target
  have hU : IsOpen U := e₁.open_target.inter e₂.open_target
  let f : E → R × S := fun y ↦ ((e₂.symm y).2,(e₁.symm y).2)
  have hf : ContDiffOn ℂ 1 f U :=
    ((contDiff_snd.comp_contDiffOn h₂).mono inter_subset_right).prodMk
      ((contDiff_snd.comp_contDiffOn h₁).mono inter_subset_left)
  let D : E → E →L[ℂ] (R × S) := fun y ↦
    ((ContinuousLinearMap.snd ℂ S R).comp (fderiv ℂ e₂.symm y)).prod
      ((ContinuousLinearMap.snd ℂ R S).comp (fderiv ℂ e₁.symm y))
  have hd (y : E) (hy : y ∈ U) : HasFDerivAt f (D y) y := by
    exact ((h₂.contDiffAt (e₂.open_target.mem_nhds hy.2)).differentiableAt
      (by norm_num)).hasFDerivAt.snd.prodMk
      (((h₁.contDiffAt (e₁.open_target.mem_nhds hy.1)).differentiableAt
      (by norm_num)).hasFDerivAt.snd)
  have hDin : Function.Injective (D p) := by
    intro v w hvw
    have hv : D p (v-w) = 0 := by rw [map_sub,hvw,sub_self]
    have ha : P p (v-w) = 0 := (hk₂ p hp₂ (v-w)).mpr (congrArg Prod.fst hv)
    have hb : P p (v-w) = v-w := (hk₁ p hp₁ (v-w)).mpr (congrArg Prod.snd hv)
    exact sub_eq_zero.mp (hb.symm.trans ha)
  let A := ((D p).toLinearMap.linearEquivOfInjective hDin L.symm.toLinearEquiv.finrank_eq).toContinuousLinearEquiv
  obtain ⟨e,he,hep,heU,hee,hei⟩ := exists_holomorphic_ift_chart hU hf ⟨hp₁,hp₂⟩ A
    (hd p ⟨hp₁,hp₂⟩)
  refine ⟨e,hep,?_,heU,hee,hei,?_⟩
  · rw [he]
    simp [f,h0₁,h0₂]
  · intro y hy v
    rw [he,(hd y (heU hy)).fderiv]
    exact ⟨hk₁ y (heU hy).1 v,hk₂ y (heU hy).2 v⟩

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_product_coordinates {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt₁ : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    (hInt₂ : ∀ O : Set E, IsOpen O → O ⊆ U →
      InvolutiveProjectionOn (fun x ↦ ContinuousLinearMap.id ℂ E-P x) O)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph E ((Fin r → ℂ) × (Fin s → ℂ)),
      p ∈ e.source ∧ e p = 0 ∧ e.source ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v,
        (P y v = v ↔ (fderiv ℂ e y v).2 = 0) ∧
        (P y v = 0 ↔ (fderiv ℂ e y v).1 = 0) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨e₁,h0₁,he₁,hU₁,_,hi₁,hk₁⟩ := holomorphic_frobenius hU P hP hid hInt₁ hp hr hs
  let Q := fun x ↦ ContinuousLinearMap.id ℂ E-P x
  have hQ : DifferentiableOn ℂ Q U := (differentiableOn_const (c := ContinuousLinearMap.id ℂ E)).sub hP
  have hidQ (x : E) (hx : x ∈ U) (v : E) : Q x (Q x v) = Q x v :=
    projection_complement_idempotent (P x) (hid x hx) v
  have hrQ : Module.finrank ℂ (LinearMap.range (Q p).toLinearMap) = s := by
    rw [projection_complement_range (P p) (hid p hp)]
    exact hs
  have hsQ : Module.finrank ℂ (LinearMap.ker (Q p).toLinearMap) = r := by
    rw [projection_complement_ker (P p) (hid p hp)]
    exact hr
  obtain ⟨e₂,h0₂,he₂,_,_,hi₂,hk₂⟩ := holomorphic_frobenius hU Q hQ hidQ hInt₂ hp hrQ hsQ
  have hp₁ : p ∈ e₁.target := he₁ ▸ e₁.map_source h0₁
  have hp₂ : p ∈ e₂.target := he₂ ▸ e₂.map_source h0₂
  have hi0₁ : e₁.symm p = 0 := by rw [← he₁,e₁.left_inv h0₁]
  have hi0₂ : e₂.symm p = 0 := by rw [← he₂,e₂.left_inv h0₂]
  obtain ⟨L,_⟩ := exists_projection_coordinates (P p) (hid p hp) hr hs
  obtain ⟨e,hep,he0,heU,he,hei,hker⟩ := combine_foliation_charts P e₁ e₂ hi₁ hi₂ hk₁
    (fun y hy v ↦ (complement_fixed_iff_zero (P y) v).symm.trans (hk₂ y hy v))
    hp₁ hp₂ hi0₁ hi0₂ L
  exact ⟨e,hep,he0,fun y hy ↦ hU₁ (heU hy).1,he,hei,hker⟩

end UniversalCoverSplitting
open Set Filter Topology
open scoped Manifold ContDiff
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

theorem local_product_chart (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (c : X.Carrier) :
    ∃ e : OpenPartialHomeomorph X.Carrier (Model r × Model s),
      c ∈ e.source ∧ e c = 0 ∧
      MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source ∧
      MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target ∧
      ∀ y ∈ e.source, ∀ v : Tangent X y,
        (S.projection y v = v ↔
          (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).2 = 0) ∧
        (S.projection y v = 0 ↔
          (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).1 = 0) := by
  let a := extChartAt (model n) c
  let P := projectionInChart S.projection c
  have hInt₁ (O : Set (Model n)) (hO : IsOpen O) (hOU : O ⊆ a.target) :
      InvolutiveProjectionOn P O := h₁ c O hO hOU
  have hInt₂ (O : Set (Model n)) (hO : IsOpen O) (hOU : O ⊆ a.target) :
      InvolutiveProjectionOn (fun z ↦ ContinuousLinearMap.id ℂ (Model n)-P z) O := by
    intro V W hV hW hVP hWP z hz
    have heq (y : Model n) (hy : y ∈ O) :=
      projectionInChart_complement S.projection c (hOU hy)
    have H := h₂ c O hO hOU V W hV hW
      (fun y hy ↦ (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (V y)) (heq y hy)).trans (hVP y hy))
      (fun y hy ↦ (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (W y)) (heq y hy)).trans (hWP y hy)) z hz
    exact (congrArg (fun L : Model n →L[ℂ] Model n ↦ L (VectorField.lieBracket ℂ V W z))
      (heq z hz)).symm.trans H
  have hr : Module.finrank ℂ (LinearMap.range (P (a c)).toLinearMap) = r := by
    have H : P (a c) = (S.projection c : Model n →L[ℂ] Model n) := projectionInChart_self S.projection c
    rw [H]
    exact S.first_rank c
  have hs : Module.finrank ℂ (LinearMap.ker (P (a c)).toLinearMap) = s := by
    have H : P (a c) = (S.projection c : Model n →L[ℂ] Model n) := projectionInChart_self S.projection c
    rw [H]
    exact S.second_rank c
  obtain ⟨b,hbc,hb0,hbU,hb,hbi,hbk⟩ := holomorphic_product_coordinates
    (isOpen_extChartAt_target c) P (S.holomorphic c)
    (fun z hz v ↦ projectionInChart_idempotent S c hz v) hInt₁ hInt₂
    (mem_extChartAt_target c) hr hs
  let d := chartAt (Model n) c
  have ha : (a : X.Carrier → Model n) = d := by
    ext x; simp [a,d,model]
  have hai : (a.symm : Model n → X.Carrier) = d.symm := by
    ext x; simp [a,d,model]
  have has : a.source = d.source := extChartAt_source (model n) c
  have hat : a.target = d.target := by
    simp [a,d,model]
  let e := d.trans b
  have hec : c ∈ e.source := ⟨mem_chart_source (Model n) c,ha ▸ hbc⟩
  have he0 : e c = 0 := by change b (d c) = 0; rw [← ha]; exact hb0
  have hd : MDifferentiableOn (model n) (model n) d d.source := by
    rw [← ha]
    exact mdifferentiableOn_extChartAt (I := model n) (x := c)
  have hdi : MDifferentiableOn (model n) (model n) d.symm d.target := by
    rw [← hai,← hat]
    exact mdifferentiableOn_extChartAt_symm
  have hbd : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) b b.source :=
    mdifferentiableOn_iff_differentiableOn.mpr (hb.differentiableOn (by norm_num))
  have hbid : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) b.symm b.target :=
    mdifferentiableOn_iff_differentiableOn.mpr (hbi.differentiableOn (by norm_num))
  have he : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source :=
    hbd.comp (hd.mono inter_subset_left) inter_subset_right
  have hei : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target :=
    hdi.comp (hbid.mono inter_subset_left) inter_subset_right
  refine ⟨e,hec,he0,he,hei,?_⟩
  intro y hy v
  change Model n at v
  have hdy : y ∈ d.source := hy.1
  have hby : d y ∈ b.source := hy.2
  have hay : a y ∈ a.target := a.map_source (has ▸ hdy)
  let A : Model n →L[ℂ] Model n := mfderiv (model n) (model n) d y
  let B : Model n →L[ℂ] Model n := mfderiv (model n) (model n) d.symm (d y)
  let T : Model n →L[ℂ] Model n := S.projection y
  have hBA : B.comp A = ContinuousLinearMap.id ℂ (Model n) := by
    have H := (chart_mfderiv_inverses c hay).2
    rw [ha,hai,d.left_inv hdy] at H
    exact H
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (Model n) := by
    have H := (chart_mfderiv_inverses c hay).1
    rw [ha,hai,d.left_inv hdy] at H
    exact H
  have hBA' (w : Model n) : B (A w) = w := congrArg (fun L : Model n →L[ℂ] Model n ↦ L w) hBA
  have hAinj : Function.Injective A := by
    intro x z hxz
    simpa only [hBA'] using congrArg B hxz
  have hPA (w : Model n) : P (d y) (A w) = A (T w) := by
    change projectionInChart S.projection c (d y) (A w) = A (T w)
    dsimp only [projectionInChart]
    rw [ha,hai,d.left_inv hdy]
    change A (T (B (A w))) = A (T w)
    rw [hBA']
  have hD : (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y :
      Model n →L[ℂ] (Model r × Model s)) = (fderiv ℂ b (d y)).comp A := by
    have H := mfderiv_comp (I := model n) (I' := model n)
      (I'' := 𝓘(ℂ, Model r × Model s)) y
      (hbd.mdifferentiableAt (b.open_source.mem_nhds hby))
      (hd.mdifferentiableAt (d.open_source.mem_nhds hdy))
    change (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y :
      Model n →L[ℂ] (Model r × Model s)) =
      (mfderiv (model n) 𝓘(ℂ, Model r × Model s) b (d y)).comp A at H
    simp only [mfderiv_eq_fderiv] at H
    exact H
  have hfin := hbk (d y) hby (A v)
  rw [hPA v] at hfin
  constructor
  · change T v = v ↔ _
    rw [hD]
    exact (hAinj.eq_iff).symm.trans hfin.1
  · change T v = 0 ↔ _
    rw [hD]
    have ha0 : A (T v) = 0 ↔ T v = 0 := by
      simpa only [map_zero] using (hAinj.eq_iff (a := T v) (b := 0))
    exact ha0.symm.trans hfin.2

end UniversalCoverSplitting
open Set Metric
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

structure SplittingChart (S : HolomorphicSplitting X r s) where
  chart : OpenPartialHomeomorph X.Carrier (Model r × Model s)
  radius : ℝ
  radius_pos : 0 < radius
  product_range : chart.target = ball 0 radius ×ˢ ball 0 radius
  holomorphic : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) chart chart.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) chart.symm chart.target
  horizontal : ∀ y ∈ chart.source, ∀ v : Tangent X y,
    S.projection y v = v ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) chart y v).2 = 0
  vertical : ∀ y ∈ chart.source, ∀ v : Tangent X y,
    S.projection y v = 0 ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) chart y v).1 = 0

theorem restrict_product_chart (S : HolomorphicSplitting X r s)
    (e : OpenPartialHomeomorph X.Carrier (Model r × Model s))
    (he : MDifferentiableOn (model n) 𝓘(ℂ, Model r × Model s) e e.source)
    (hei : MDifferentiableOn 𝓘(ℂ, Model r × Model s) (model n) e.symm e.target)
    (hk : ∀ y ∈ e.source, ∀ v : Tangent X y,
      (S.projection y v = v ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).2 = 0) ∧
      (S.projection y v = 0 ↔ (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e y v).1 = 0))
    {c : X.Carrier} (hc : c ∈ e.source) (h0 : e c = 0) :
    ∃ b : SplittingChart S, c ∈ b.chart.source ∧ b.chart c = 0 := by
  have h0t : (0 : Model r × Model s) ∈ e.target := h0 ▸ e.map_source hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds h0t)
  let V : Set (Model r × Model s) := ball 0 ε ×ˢ ball 0 ε
  have hV : IsOpen V := isOpen_ball.prod isOpen_ball
  have hVU : V ⊆ e.target := by
    rw [show V = ball (0 : Model r × Model s) ε from ball_prod_same _ _ _]
    exact hball
  let b := (e.symm.restrOpen V hV).symm
  have hbt : b.target = V := inter_eq_right.mpr hVU
  have hbc : c ∈ b.source := by
    change c ∈ e.source ∧ e c ∈ V
    refine ⟨hc,?_⟩
    rw [h0]
    exact ⟨mem_ball_self hε,mem_ball_self hε⟩
  let B : SplittingChart S :=
    { chart := b
      radius := ε
      radius_pos := hε
      product_range := hbt
      holomorphic := he.mono inter_subset_left
      inverse_holomorphic := hei.mono inter_subset_left
      horizontal := fun y hy v ↦ (hk y hy.1 v).1
      vertical := fun y hy v ↦ (hk y hy.1 v).2 }
  exact ⟨B,hbc,h0⟩

end UniversalCoverSplitting

namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n}

theorem exists_splittingChart (S : HolomorphicSplitting X r s)
    (h₁ : Integrable S.projection) (h₂ : Integrable (complementaryProjection S))
    (c : X.Carrier) :
    ∃ b : SplittingChart S, c ∈ b.chart.source ∧ b.chart c = 0 := by
  obtain ⟨e,hc,h0,he,hei,hk⟩ := local_product_chart S h₁ h₂ c
  exact restrict_product_chart S e he hei hk hc h0
end UniversalCoverSplitting
open Set Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma SplittingChart.inverse_derivative (e : SplittingChart S)
    {z : Model r × Model s} (hz : z ∈ e.chart.target) (w : Model r × Model s) :
    mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (e.chart.symm z)
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm z w) = w := by
  have hdi := e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds hz)
  have hd := e.holomorphic.mdifferentiableAt
    (e.chart.open_source.mem_nhds (e.chart.map_target hz))
  have hEq : (e.chart ∘ e.chart.symm : (Model r × Model s) → Model r × Model s) =ᶠ[𝓝 z] id := by
    filter_upwards [e.chart.open_target.mem_nhds hz] with y hy
    exact e.chart.right_inv hy
  have h := mfderiv_comp z hd hdi
  change (mfderiv 𝓘(ℂ, Model r × Model s) 𝓘(ℂ, Model r × Model s)
    (e.chart ∘ e.chart.symm) z : (Model r × Model s) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (e.chart.symm z)).comp
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm z) at h
  have hid := hEq.mfderiv_eq (I := 𝓘(ℂ, Model r × Model s)) (I' := 𝓘(ℂ, Model r × Model s))
  simp only [mfderiv_id] at hid
  have h' := h.symm.trans hid
  exact congrArg (fun A : (Model r × Model s) →L[ℂ] (Model r × Model s) ↦ A w) h'

theorem SplittingChart.box_coordinates (e : SplittingChart S)
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {f : ℂ × ℂ → X.Carrier}
    (hf : IsBox S U f) (hmap : MapsTo f U e.chart.source) :
    DifferentiableOn ℂ (e.chart ∘ f) U ∧
      ∀ z ∈ U,
        (fderiv ℂ (e.chart ∘ f) z (1,0)).2 = 0 ∧
        (fderiv ℂ (e.chart ∘ f) z (0,1)).1 = 0 := by
  refine ⟨mdifferentiableOn_iff_differentiableOn.mp (e.holomorphic.comp hf.1 hmap),?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.holomorphic.mdifferentiableAt (e.chart.open_source.mem_nhds (hmap hz)))
    (hf.1.mdifferentiableAt (hU.mem_nhds hz))
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, Model r × Model s) (e.chart ∘ f) z :
    (ℂ × ℂ) →L[ℂ] (Model r × Model s)) =
    (mfderiv (model n) 𝓘(ℂ, Model r × Model s) e.chart (f z)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) f z) at h
  simp only [mfderiv_eq_fderiv] at h
  rw [h]
  exact ⟨(e.horizontal _ (hmap hz) _).mp (hf.2 z hz).1,
    (e.vertical _ (hmap hz) _).mp (hf.2 z hz).2⟩

theorem SplittingChart.box_of_coordinate_tangencies (e : SplittingChart S)
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) {g : ℂ × ℂ → Model r × Model s}
    (hg : DifferentiableOn ℂ g U) (hmap : MapsTo g U e.chart.target)
    (ht : ∀ z ∈ U, (fderiv ℂ g z (1,0)).2 = 0 ∧ (fderiv ℂ g z (0,1)).1 = 0) :
    IsBox S U (e.chart.symm ∘ g) := by
  refine ⟨e.inverse_holomorphic.comp (mdifferentiableOn_iff_differentiableOn.mpr hg) hmap,?_⟩
  intro z hz
  have h := mfderiv_comp z
    (e.inverse_holomorphic.mdifferentiableAt (e.chart.open_target.mem_nhds (hmap hz)))
    (mdifferentiableAt_iff_differentiableAt.mpr (hg.differentiableAt (hU.mem_nhds hz)))
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) (e.chart.symm ∘ g) z : (ℂ × ℂ) →L[ℂ] Model n) =
    (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm (g z)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, Model r × Model s) g z) at h
  simp only [mfderiv_eq_fderiv] at h
  have hp (v : ℂ × ℂ) :
      (mfderiv 𝓘(ℂ, ℂ × ℂ) (model n) (e.chart.symm ∘ g) z : (ℂ × ℂ) →L[ℂ] Model n) v =
      (mfderiv 𝓘(ℂ, Model r × Model s) (model n) e.chart.symm (g z) :
        (Model r × Model s) →L[ℂ] Model n) (fderiv ℂ g z v) := by
    exact congrArg (fun A : (ℂ × ℂ) →L[ℂ] Model n ↦ A v) h
  constructor
  · apply (e.horizontal _ (e.chart.map_target (hmap hz)) _).mpr
    rw [hp]
    rw [e.inverse_derivative (hmap hz)]
    exact (ht z hz).1
  · apply (e.vertical _ (e.chart.map_target (hmap hz)) _).mpr
    rw [hp]
    rw [e.inverse_derivative (hmap hz)]
    exact (ht z hz).2

end UniversalCoverSplitting

end

end OAI
