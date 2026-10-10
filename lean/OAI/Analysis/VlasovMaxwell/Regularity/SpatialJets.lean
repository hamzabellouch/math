import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.SlabEquations

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

def SpatiallySmoothSlab {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (T : ℝ) (F : ℝ × U → W) : Prop :=
  (∀ t∈Icc (0:ℝ) T, ContDiff ℝ ∞ (fun x => F (t,x))) ∧
    ∀ k : ℕ, ContinuousOn (fun p : ℝ × U => iteratedFDeriv ℝ k (fun x => F (p.1,x)) p.2)
      {p | p.1∈Icc (0:ℝ) T}

lemma spatiallySmoothSlab_of_uniform_jets {U W : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {T : ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈Icc (0:ℝ) T → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => F n (t,y)) x‖≤C)
    (hl : TendstoUniformlyOn F f atTop {p | p.1∈Icc (0:ℝ) T}) :
    SpatiallySmoothSlab T f := by
  refine ⟨?_,?_⟩
  · intro t ht
    rw [contDiff_infty]
    exact fun n => (smooth_spatial_limit_nat n hF hb hl).1 t ht
  · exact fun n => (smooth_spatial_limit_nat n hF hb hl).2.1

theorem exists_local_spatially_smooth_classical (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T ∧
      SpatiallySmoothSlab T s.f ∧ SpatiallySmoothSlab T s.E ∧ SpatiallySmoothSlab T s.B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,E,B,hS0,hsm,hc,hr,hg,hEl,hBl,hEc,hBc,hcLim⟩ :=
    exists_picard_field_limit hd
  have hjets := uniform_picard_sequence_jets hd hT hT1 hN.le hM hS0 hsm hc hr
  obtain ⟨Q,hQ,hQEB,hQf⟩ := hjets 1
  have hQ0 : 0≤Q := zero_le_one.trans hQ
  have hcurv : ∀ n, SpatialFieldCurvature T (2*Q) (S n).E (S n).B := by
    intro n t ht
    exact ⟨curvature_of_second_derivative_bound ((hsm n).1.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).1),
      curvature_of_second_derivative_bound ((hsm n).2.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).2)⟩
  have hcurvf : ∀ n, PhaseParticleCurvature T (2*Q) (S (n+1)).f := by
    intro n t ht
    exact curvature_of_second_derivative_bound ((hr n).1.smooth_f.comp (contDiff_const.prodMk contDiff_id)) hQ0
      (hQf n t ht 2 le_rfl)
  obtain ⟨f,hfl,hfc,hfn,hfi,hfb,hfLip⟩ := picard_particle_limit hd hT.le hL.le hN.le hsm hc hr hg
  obtain ⟨hfC,hEC,hBC,heq⟩ := local_c1_limit_of_picard (s:=⟨f,E,B⟩) hT (by positivity) (by positivity) hM hL.le
    (fun n => (hr n).1) (fun n => (hr n).2.1) hcurv hcurvf (fun n => (hr n).2.2.1)
    (fun n => (hr n).2.2.2) hcLim.1 hfb hfc hfl hEl hBl
  have hEi (x : Vec) : E (0,x)=d.E₀ x := by
    have hh := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_E] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hBi (x : Vec) : B (0,x)=d.B₀ x := by
    have hh := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_B] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hL2 := picard_limit_slab_l2 hT.le hEC.continuousOn hBC.continuousOn hsm
    (fun n => (hr n).1) (fun n => (hr n).2.1) (fun n => (hr n).2.2.1) hEl hBl
  refine ⟨T,hT,⟨f,E,B⟩,⟨hfC,hEC,hBC,hfn,hL2.1,hL2.2,hfb.compact,heq.equationsBefore,hfi,hEi,hBi⟩,
    heq,?_,?_,?_⟩
  · apply spatiallySmoothSlab_of_uniform_jets (fun n => (hr n).1.smooth_f) _ hfl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht z => hQf n t ht k (by omega) z⟩
  · apply spatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).1) _ hEl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).1⟩
  · apply spatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).2) _ hBl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).2⟩

universe u

def SpatialJetRegular {U W : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ∞) (J : Set ℝ) (F : ℝ × U → W) : Prop :=
  (∀ t∈J, ContDiff ℝ ∞ (fun x => F (t,x))) ∧
    ∀ j : ℕ, ContDiffOn ℝ n (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => F (p.1,x)) p.2) {p | p.1∈J}

variable {U V W Z : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {n : ℕ∞} {J : Set ℝ}

lemma SpatiallySmoothSlab.spatialJetRegular {F : ℝ × U → W} {T : ℝ}
    (hF : SpatiallySmoothSlab T F) : SpatialJetRegular 0 (Icc 0 T) F :=
  ⟨hF.1,fun j => contDiffOn_zero.mpr (hF.2 j)⟩

lemma SpatialJetRegular.regular {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    ContDiffOn ℝ n F {p | p.1∈J} := by
  have h := (continuousMultilinearCurryFin0 ℝ U W).contDiff.comp_contDiffOn (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply,Prod.mk.eta] using h

lemma SpatialJetRegular.deriv {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    SpatialJetRegular n J (fun p : ℝ × U => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  refine ⟨fun t ht => (hF.1 t ht).fderiv_right (m:=∞) (by simp),fun j => ?_⟩
  let A : (U [×(j+1)]→L[ℝ] W) →L[ℝ] (U [×j]→L[ℝ] U →L[ℝ] W) :=
    (continuousMultilinearCurryRightEquiv' ℝ j U W).toContinuousLinearEquiv.toContinuousLinearMap
  have he := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=U [×(j+1)]→L[ℝ] W)
    (F:=U [×j]→L[ℝ] U →L[ℝ] W) (n:=(n:ℕ∞ω)) A
  have h := he.comp_contDiffOn (hF.2 (j+1))
  simpa [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def] using h

lemma SpatialJetRegular.clm {F : ℝ × U → V} (hF : SpatialJetRegular n J F) (L : V →L[ℝ] W) :
    SpatialJetRegular n J (fun p => L (F p)) := by
  refine ⟨fun t ht => L.contDiff.comp (hF.1 t ht),fun j => ?_⟩
  let A := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => U) V W) L
  have h := A.contDiff.comp_contDiffOn (hF.2 j)
  apply h.congr
  intro p hp
  exact L.iteratedFDeriv_comp_left (hF.1 p.1 hp).contDiffAt (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))

lemma SpatialJetRegular.add {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (hG : SpatialJetRegular n J G) : SpatialJetRegular n J (fun p => F p+G p) := by
  refine ⟨fun t ht => (hF.1 t ht).add (hG.1 t ht),fun j => ?_⟩
  apply ((hF.2 j).add (hG.2 j)).congr
  intro p hp
  exact congrFun (iteratedFDeriv_add
    ((hF.1 p.1 hp).of_le (show (j:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))) ((hG.1 p.1 hp).of_le (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)))) p.2

lemma SpatialJetRegular.congr {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (he : ∀ p : ℝ × U, p.1∈J → G p=F p) : SpatialJetRegular n J G := by
  have hs (t : ℝ) (ht : t∈J) : (fun x => G (t,x))=(fun x => F (t,x)) := funext fun x => he (t,x) ht
  refine ⟨fun t ht => by rw [hs t ht]; exact hF.1 t ht,fun j => ?_⟩
  apply (hF.2 j).congr
  intro p hp
  rw [hs p.1 hp]

lemma spatialJetRegular_bilinear_jet (j : ℕ) :
    ∀ {V W Z : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (B : V →L[ℝ] W →L[ℝ] Z) {F : ℝ × U → V} {G : ℝ × U → W},
      SpatialJetRegular n J F → SpatialJetRegular n J G →
      ContDiffOn ℝ n (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => B (F (p.1,x)) (G (p.1,x))) p.2)
        {p | p.1∈J} := by
  induction j with
  | zero =>
    intro V W Z _ _ _ _ _ _ B F G hF hG
    have h := ((B.contDiff.comp_contDiffOn hF.regular).clm_apply hG.regular)
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ U Z).symm.contDiff.comp_contDiffOn h
  | succ j ih =>
    intro V W Z _ _ _ _ _ _ B F G hF hG
    let DF := fun p : ℝ × U => fderiv ℝ (fun x => F (p.1,x)) p.2
    let DG := fun p : ℝ × U => fderiv ℝ (fun x => G (p.1,x)) p.2
    have h1 := ih (B.precompR U) hF hG.deriv
    have h2 := ih (B.precompL U) hF.deriv hG
    have h := (continuousMultilinearCurryRightEquiv' ℝ j U Z).symm.contDiff.comp_contDiffOn (h1.add h2)
    apply h.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
    congr 1
    have he : fderiv ℝ (fun x => B (F (p.1,x)) (G (p.1,x))) =
        fun x => B.precompR U (F (p.1,x)) (DG (p.1,x)) + B.precompL U (DF (p.1,x)) (G (p.1,x)) := by
      funext x
      exact B.fderiv_of_bilinear ((hF.1 p.1 hp).differentiable (by simp) x)
        ((hG.1 p.1 hp).differentiable (by simp) x)
    rw [he]
    have hR : ContDiff ℝ ∞ (fun x => B.precompR U (F (p.1,x)) (DG (p.1,x))) :=
      by
        have hB : ContDiff ℝ ∞ (B.precompR U) := ContinuousLinearMap.contDiff _
        exact (hB.comp (hF.1 p.1 hp)).clm_apply (hG.deriv.1 p.1 hp)
    have hL : ContDiff ℝ ∞ (fun x => B.precompL U (DF (p.1,x)) (G (p.1,x))) :=
      by
        have hB : ContDiff ℝ ∞ (B.precompL U) := ContinuousLinearMap.contDiff _
        exact (hB.comp (hF.deriv.1 p.1 hp)).clm_apply (hG.1 p.1 hp)
    have hj : (j:ℕ∞ω)≤∞ := by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)
    exact congrFun (iteratedFDeriv_add (hR.of_le hj) (hL.of_le hj)) p.2

lemma SpatialJetRegular.bilinear {F : ℝ × U → V} {G : ℝ × U → W}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) (B : V →L[ℝ] W →L[ℝ] Z) :
    SpatialJetRegular n J (fun p => B (F p) (G p)) := by
  exact ⟨fun t ht => (B.contDiff.comp (hF.1 t ht)).clm_apply (hG.1 t ht),
    fun j => spatialJetRegular_bilinear_jet j B hF hG⟩

end

section
universe u
variable {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] {n : ℕ∞} {J : Set ℝ}

lemma spatialJetRegular_iterated (j : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × U → W},
      SpatialJetRegular n J F → SpatialJetRegular n J
        (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => F (p.1,x)) p.2) := by
  induction j with
  | zero =>
    intro W _ _ F hF
    let A : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using hF.clm A
  | succ j ih =>
    intro W _ _ F hF
    let A : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using (ih hF.deriv).clm A

lemma SpatialJetRegular.mono_order {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} {m : ℕ∞} (hF : SpatialJetRegular n J F) (h : m≤n) : SpatialJetRegular m J F :=
  ⟨hF.1,fun j => (hF.2 j).of_le (by exact_mod_cast h)⟩

end

universe u
variable {U V W Z : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {n : ℕ∞} {J : Set ℝ}

lemma SpatialJetRegular.precomp {F : ℝ × V → W} (hF : SpatialJetRegular n J F) (L : U →L[ℝ] V) :
    SpatialJetRegular n J (fun p : ℝ × U => F (p.1,L p.2)) := by
  refine ⟨fun t ht => (hF.1 t ht).comp L.contDiff,fun j => ?_⟩
  let A : (V [×j]→L[ℝ] W) →L[ℝ] (U [×j]→L[ℝ] W) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => L)
  have h := A.contDiff.comp_contDiffOn ((hF.2 j).comp
    (contDiffOn_fst.prodMk (L.contDiff.comp_contDiffOn contDiffOn_snd)) (fun p hp => hp))
  apply h.congr
  intro p hp
  exact L.iteratedFDeriv_comp_right (hF.1 p.1 hp) p.2
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))

lemma spatialJetRegular_fixed {F : U → W} (hF : ContDiff ℝ ∞ F) :
    SpatialJetRegular n J (fun p : ℝ × U => F p.2) := by
  refine ⟨fun _ _ => hF,fun j => ?_⟩
  exact ((hF.iteratedFDeriv_right (m:=∞) (i:=j) (by exact_mod_cast (le_top : (⊤:ℕ∞)+(j:ℕ∞)≤⊤))).of_le
    (by exact_mod_cast (le_top : n≤⊤))).comp_contDiffOn contDiffOn_snd

lemma SpatialJetRegular.neg {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    SpatialJetRegular n J (fun p => -F p) := by
  simpa using hF.clm (-(ContinuousLinearMap.id ℝ W))

lemma SpatialJetRegular.sub {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (hG : SpatialJetRegular n J G) : SpatialJetRegular n J (fun p => F p-G p) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma SpatialJetRegular.prodMk {F : ℝ × U → V} {G : ℝ × U → W}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) :
    SpatialJetRegular n J (fun p => (F p,G p)) := by
  convert (hF.clm (ContinuousLinearMap.inl ℝ V W)).add
    (hG.clm (ContinuousLinearMap.inr ℝ V W)) using 1
  simp

lemma SpatialJetRegular.clm_comp_const {F : ℝ × U → (V →L[ℝ] W)}
    (hF : SpatialJetRegular n J F) (L : Z →L[ℝ] V) :
    SpatialJetRegular n J (fun p => (F p).comp L) := by
  exact hF.clm ((ContinuousLinearMap.compL ℝ Z V W).flip L)

lemma SpatialJetRegular.clm_apply {F : ℝ × U → (V →L[ℝ] W)} {G : ℝ × U → V}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) :
    SpatialJetRegular n J (fun p => F p (G p)) :=
  hF.bilinear hG (ContinuousLinearMap.id ℝ (V →L[ℝ] W))

end


open Set Filter Metric MeasureTheory
open scoped Topology

lemma hasFDerivWithinAt_integral_dominated
    {A H E : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : H → A → E} {F' : A → H →L[ℝ] E} {s : Set H} {x₀ : H} {b : A → ℝ}
    (hF : ∀ᶠ x in 𝓝[s] x₀, Integrable (F x) μ) (hF₀ : Integrable (F x₀) μ)
    (hF' : Integrable F' μ) (hb : Integrable b μ) (hbn : ∀ a, 0 ≤ b a)
    (hlip : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a-F x₀ a‖ ≤ b a*‖x-x₀‖)
    (hd : ∀ᵐ a ∂μ, HasFDerivWithinAt (F · a) (F' a) s x₀) :
    HasFDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) s x₀ := by
  have hn (x : H) : 0 ≤ ‖x-x₀‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have he : ∀ᶠ x in 𝓝[s] x₀,
      ‖x-x₀‖⁻¹ * ‖((∫ a, F x a ∂μ)-(∫ a, F x₀ a ∂μ))-(∫ a, F' a ∂μ) (x-x₀)‖ =
      ‖∫ a, ‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀)) ∂μ‖ := by
    filter_upwards [hF] with x hx
    rw [← norm_smul_of_nonneg (hn _), integral_smul, integral_sub,
      integral_sub, ← ContinuousLinearMap.integral_apply hF']
    exacts [hx, hF₀, hx.sub hF₀, hF'.apply_continuousLinearMap _]
  rw [hasFDerivWithinAt_iff_tendsto, tendsto_congr' he,
    ← tendsto_zero_iff_norm_tendsto_zero,
    ← show (∫ a : A, ‖x₀-x₀‖⁻¹ • (F x₀ a-F x₀ a-F' a (x₀-x₀)) ∂μ)=0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun a => b a+‖F' a‖)
  · filter_upwards [hF] with x hx
    exact ((hx.aestronglyMeasurable.sub hF₀.aestronglyMeasurable).sub
      (hF'.aestronglyMeasurable.apply_continuousLinearMap _)).const_smul _
  · filter_upwards [hlip] with x hx
    filter_upwards [hx] with a ha
    calc
      ‖‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀))‖
        ≤ ‖x-x₀‖⁻¹ * (‖F x a-F x₀ a‖+‖F' a (x-x₀)‖) := by
          rw [norm_smul_of_nonneg (hn _)]; gcongr; exact norm_sub_le _ _
      _ ≤ ‖x-x₀‖⁻¹ * (b a*‖x-x₀‖+‖F' a‖*‖x-x₀‖) := by
          gcongr; exact (F' a).le_opNorm _
      _ ≤ b a+‖F' a‖ := by
          rw [← add_mul, ← div_eq_inv_mul]
          have hab := hbn a
          apply div_le_of_le_mul₀ <;> first | rfl | positivity
  · exact hb.add hF'.norm
  · filter_upwards [hd] with a ha
    suffices Tendsto (fun x => ‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀)))
        (𝓝[s] x₀) (𝓝 0) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun x => ‖x-x₀‖⁻¹ * ‖F x a-F x₀ a-F' a (x-x₀)‖) =
        (fun x => ‖‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀))‖) := by
      funext x; rw [norm_smul_of_nonneg (hn x)]
    rwa [hasFDerivWithinAt_iff_tendsto,heq] at ha


section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section
universe u
section Differentiation
variable {H A W : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {S : Set H} {F : H → A → W} {D : H → A → H →L[ℝ] W}

lemma hasFDerivWithinAt_integral_compactFamily (hSc : IsClosed S) (hSv : Convex ℝ S)
    (hF : ContinuousOn F.uncurry (S ×ˢ univ)) (hD : ContinuousOn D.uncurry (S ×ˢ univ))
    (hd : ∀ x∈S, ∀ a, HasFDerivWithinAt (fun y => F y a) (D x a) S x)
    {x : H} (hx : x∈S) :
    HasFDerivWithinAt (fun y => ∫ a, F y a ∂μ) (∫ a, D x a ∂μ) S x := by
  have hc {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      {G : H → A → Z} (hG : ContinuousOn G.uncurry (S ×ˢ univ)) {y : H} (hy : y∈S) :
      Continuous (G y) := by
    apply continuousOn_univ.mp
    exact hG.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun a _ => ⟨hy,mem_univ a⟩)
  have hi (y : H) (hy : y∈S) : Integrable (F y) μ :=
    (hc hF hy).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (D x) μ :=
    (hc hD hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let K := S ∩ closedBall x 1
  have hK : IsCompact K := (isCompact_closedBall x 1).inter_left hSc
  obtain ⟨C,hC⟩ := ((hK.prod isCompact_univ).image_of_continuousOn
    (hD.mono (fun p hp => ⟨hp.1.1,hp.2⟩))).isBounded.exists_norm_le
  let B := max C 0
  have hB : 0≤B := le_max_right _ _
  have hb (y : H) (hy : y∈K) (a : A) : ‖D y a‖≤B :=
    (hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩).trans (le_max_left _ _)
  have hxl : x∈K := ⟨hx,mem_closedBall_self (by norm_num)⟩
  have hnear : ∀ᶠ y in 𝓝[S] x, y∈K :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (by norm_num)))
  apply hasFDerivWithinAt_integral_dominated
    (hF:=Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ y in 𝓝[S] x, y∈S) (fun y hy => hi y hy)) (hF₀:=hi x hx)
    (hF':=hiD) (b:=fun _ => B) (hb:=integrable_const _) (hbn:=fun _ => hB)
  · filter_upwards [hnear] with y hy
    exact ae_of_all _ fun a => Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hd z hz.1 a).mono inter_subset_left) (fun z hz => hb z hz a)
      (hSv.inter (convex_closedBall x 1)) hxl hy
  · exact ae_of_all _ (hd x hx)
end Differentiation

variable {H V A : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ] {v : A → V} (hv : Continuous v)
  {S : Set H} (hSc : IsClosed S) (hSv : Convex ℝ S) (hSu : UniqueDiffOn ℝ S)

include hv hSc hSv hSu in

lemma contDiffOn_integral_compact_parameter_nat (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : H × V → W}, ContDiffOn ℝ n F (S ×ˢ univ) →
      ContDiffOn ℝ n (fun x => ∫ a, F (x,v a) ∂μ) S := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiffOn_zero.mpr
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ
    · exact hF.continuousOn.comp
        ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn) (fun p hp => ⟨hp.1,mem_univ _⟩)
    · intro x a _ ha; exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    have hu := hSu.prod (uniqueDiffOn_univ (𝕜:=ℝ) (E:=V))
    have hn : (↑(n+1) : ℕ∞ω)=(n:ℕ∞ω)+1 := by simp
    rw [hn] at hF ⊢
    let D := fderivWithin ℝ F (S ×ˢ univ)
    have hD : ContDiffOn ℝ n D (S ×ˢ univ) := hF.fderivWithin hu le_rfl
    let L : H →L[ℝ] H × V := ContinuousLinearMap.inl ℝ H V
    have hd (x : H) (hx : x∈S) : HasFDerivWithinAt
        (fun y => ∫ a, F (y,v a) ∂μ) (∫ a, (D (x,v a)).comp L ∂μ) S x := by
      refine hasFDerivWithinAt_integral_compactFamily (μ:=μ)
        (F:=fun y a => F (y,v a)) (D:=fun y a => (D (y,v a)).comp L) hSc hSv ?_ ?_ ?_ hx
      · exact hF.continuousOn.comp
          ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn) (fun p hp => ⟨hp.1,mem_univ _⟩)
      · exact (hD.continuousOn.comp
          ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn)
          (fun p hp => ⟨hp.1,mem_univ _⟩)).clm_comp continuousOn_const
      · intro y hy a
        have hi : HasFDerivWithinAt (fun z : H => (z,v a)) L S y := by
          convert ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (v a) y)).hasFDerivWithinAt (s:=S) using 1 <;> rfl
        have ho : HasFDerivWithinAt F (D (y,v a)) (S ×ˢ univ) (y,v a) :=
          (hF.differentiableOn (by simp) (y,v a) ⟨hy,mem_univ _⟩).hasFDerivWithinAt
        exact ho.comp y hi (show MapsTo (fun z : H => (z,v a)) S (S ×ˢ (univ : Set V)) from fun z hz => ⟨hz,mem_univ _⟩)
    rw [contDiffOn_succ_iff_fderivWithin hSu]
    refine ⟨fun x hx => (hd x hx).differentiableWithinAt,by simp,?_⟩
    have he (x : H) (hx : x∈S) : fderivWithin ℝ (fun y => ∫ a, F (y,v a) ∂μ) S x =
        ∫ a, (D (x,v a)).comp L ∂μ := (hd x hx).fderivWithin (hSu x hx)
    exact (ih (hD.clm_comp contDiffOn_const)).congr he

end

universe u
variable {U V A : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ] {v : A → V} (hv : Continuous v)
  {T : ℝ} (hT : 0<T) (n : ℕ)

omit [SecondCountableTopology A] in
include hv hT in
lemma contDiffOn_integral_spatialJet
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F) :
    ContDiffOn ℝ n (fun p : ℝ × U => ∫ a, F (p.1,p.2,v a) ∂μ) {p | p.1∈Icc 0 T} := by
  have hs : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
  apply contDiffOn_integral_compact_parameter_nat (μ:=μ)
    (F:=fun p : (ℝ × U) × V => F (p.1.1,p.1.2,p.2)) hv
    (isClosed_Icc.preimage continuous_fst)
    (by simpa only [Set.preimage,hs] using (convex_Icc (𝕜:=ℝ) 0 T).prod (convex_univ (𝕜:=ℝ) (E:=U)))
    (by simpa only [Set.preimage,hs] using (uniqueDiffOn_Icc hT).prod (uniqueDiffOn_univ (𝕜:=ℝ) (E:=U))) n
  exact hF.regular.comp
    (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd)) (fun p hp => hp.1)

omit [ProperSpace U] [CompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] in
include hv in
lemma spatialJet_compactFamily
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F)
    {t : ℝ} (ht : t∈Icc 0 T) :
    SmoothCompactFamily (fun a x => F (t,x,v a)) := by
  apply SmoothCompactFamily.ofJoint (G:=fun p : V × U => F (t,p.2,p.1))
  · exact (hF.1 t ht).comp (contDiff_snd.prodMk contDiff_fst)
  · exact hv

include hv in
lemma fderiv_integral_spatialJet
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F)
    {t : ℝ} (ht : t∈Icc 0 T) (x : U) :
    fderiv ℝ (fun y => ∫ a, F (t,y,v a) ∂μ) x =
      ∫ a, (fderiv ℝ (fun z => F (t,z)) (x,v a)).comp (ContinuousLinearMap.inl ℝ U V) ∂μ := by
  rw [(hasFDerivAt_integral_smoothFamily μ (spatialJet_compactFamily hv n hF ht) x).fderiv]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  have hi : HasFDerivAt (fun y : U => (y,v a)) (ContinuousLinearMap.inl ℝ U V) x := by
    convert ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (v a) x)) using 1 <;> rfl
  exact (((hF.1 t ht).differentiable (by simp) (x,v a)).hasFDerivAt.comp x hi).fderiv

include hv hT in
lemma spatialJetRegular_integral_jet (j : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : ℝ × (U × V) → W}, SpatialJetRegular n (Icc 0 T) F →
      ContDiffOn ℝ n (fun p : ℝ × U =>
        iteratedFDeriv ℝ j (fun x => ∫ a, F (p.1,x,v a) ∂μ) p.2) {p | p.1∈Icc 0 T} := by
  induction j with
  | zero =>
    intro W _ _ _ F hF
    let C : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [C,iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      C.contDiff.comp_contDiffOn (contDiffOn_integral_spatialJet hv hT n hF)
  | succ j ih =>
    intro W _ _ _ F hF
    let G := fun p : ℝ × (U × V) =>
      (fderiv ℝ (fun z => F (p.1,z)) p.2).comp (ContinuousLinearMap.inl ℝ U V)
    have hG : SpatialJetRegular n (Icc 0 T) G := hF.deriv.clm_comp_const _
    let C : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hh := C.contDiff.comp_contDiffOn (ih hG)
    apply hh.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
    change _=C _
    have he : fderiv ℝ (fun x => ∫ a, F (p.1,x,v a) ∂μ) =
        (fun x => ∫ a, G (p.1,x,v a) ∂μ) := by
      funext x; exact fderiv_integral_spatialJet hv n hF hp x
    rw [he]
    rfl

include hv hT in
lemma SpatialJetRegular.integral_compact
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F) :
    SpatialJetRegular n (Icc 0 T) (fun p : ℝ × U => ∫ a, F (p.1,p.2,v a) ∂μ) := by
  refine ⟨fun t ht => contDiff_integral_smoothFamily μ (spatialJet_compactFamily hv n hF ht),?_⟩
  exact fun j => spatialJetRegular_integral_jet hv hT n j hF

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

universe u
variable {U W : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {J : Set ℝ} {F G : ℝ × U → W}

omit [ProperSpace U] [CompleteSpace W] in
lemma SpatialJetRegular.compactTimeFamily (hF : SpatialJetRegular 0 J F)
    {a b : ℝ} (hsub : Icc a b ⊆ J) :
    SmoothCompactFamily (fun t : Icc a b => fun x => F (t,x)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  refine ⟨fun t => hF.1 t (hsub t.property),fun j => ?_⟩
  exact (hF.2 j).continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    (fun p => hsub p.2.property)

omit [CompleteSpace W] in
attribute [local instance] Measure.Subtype.measureSpace in
lemma SpatialJetRegular.hasFDerivAt_timeIntegral (hF : SpatialJetRegular 0 J F)
    {a b : ℝ} (hab : a≤b) (hsub : Icc a b ⊆ J) (x : U) :
    HasFDerivAt (fun y => ∫ r in a..b, F (r,y))
      (∫ r in a..b, fderiv ℝ (fun y => F (r,y)) x) x := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := hasFDerivAt_integral_smoothFamily (volume : Measure (Icc a b))
    (hF.compactTimeFamily hsub) x
  have he (y : U) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, fderiv ℝ (fun y => F ((r:ℝ),y)) x) =
      ∫ r in a..b, fderiv ℝ (fun y => F (r,y)) x := by
    rw [integral_subtype measurableSet_Icc (fun r => fderiv ℝ (fun y => F (r,y)) x),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simpa only [he,he'] using hh

lemma space_time_derivative_interval (hF : SpatialJetRegular 0 J F) (hG : SpatialJetRegular 0 J G)
    (htime : ∀ t∈J, ∀ x, HasDerivAt (fun r => F (r,x)) (G (t,x)) t)
    {a b t : ℝ} (hsub : Icc a b ⊆ J) (ht : t∈Ioo a b) (x : U) :
    HasDerivAt (fun r => fderiv ℝ (fun y => F (r,y)) x)
      (fderiv ℝ (fun y => G (t,y)) x) t := by
  let DF := fun r => fderiv ℝ (fun y => F (r,y)) x
  let DG := fun r => fderiv ℝ (fun y => G (r,y)) x
  have hcG (y : U) : ContinuousOn (fun r => G (r,y)) (Icc a b) :=
    hG.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun r hr => hsub hr)
  have hcDG : ContinuousOn DG (Icc a b) :=
    hG.deriv.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun r hr => hsub hr)
  have he (r : ℝ) (hr : r∈Ioo a b) : DF r = DF a+∫ u in a..r, DG u := by
    have hsub' : Icc a r ⊆ J := fun u hu => hsub ⟨hu.1,hu.2.trans hr.2.le⟩
    have hgi (y : U) : IntervalIntegrable (fun u => G (u,y)) volume a r :=
      ContinuousOn.intervalIntegrable_of_Icc hr.1.le (hcG y |>.mono (Icc_subset_Icc_right hr.2.le))
    have heq : (fun y => ∫ u in a..r, G (u,y)) = (fun y => F (r,y)-F (a,y)) := by
      funext y
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro u hu
        rw [uIcc_of_le hr.1.le] at hu
        exact htime u (hsub' hu) y
      · exact hgi y
    have hd := hG.hasFDerivAt_timeIntegral hr.1.le hsub' x
    rw [heq] at hd
    have hdf := (((hF.1 r (hsub ⟨hr.1.le,hr.2.le⟩)).differentiable (by simp) x).hasFDerivAt.sub
      (((hF.1 a (hsub ⟨le_rfl,hr.1.le.trans hr.2.le⟩)).differentiable (by simp) x).hasFDerivAt))
    have hh := hd.unique hdf
    change (∫ u in a..r, DG u)=DF r-DF a at hh
    rw [hh]
    abel
  have hgi : IntervalIntegrable DG volume a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1.le (hcDG.mono (Icc_subset_Icc_right ht.2.le))
  have hgopen : ContinuousOn DG (Ioo a b) := hcDG.mono Ioo_subset_Icc_self
  have hd := intervalIntegral.integral_hasDerivAt_right hgi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hgopen t ht)
    (hgopen.continuousAt (Ioo_mem_nhds ht.1 ht.2))
  exact (hd.const_add (DF a)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun r hr => he r hr)

lemma space_time_derivative_open (hJ : IsOpen J) (hF : SpatialJetRegular 0 J F)
    (hG : SpatialJetRegular 0 J G)
    (htime : ∀ t∈J, ∀ x, HasDerivAt (fun r => F (r,x)) (G (t,x)) t)
    {t : ℝ} (ht : t∈J) (x : U) :
    HasDerivAt (fun r => fderiv ℝ (fun y => F (r,y)) x)
      (fderiv ℝ (fun y => G (t,y)) x) t := by
  obtain ⟨ε,hε,hεJ⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht)
  apply space_time_derivative_interval hF hG htime (a:=t-ε/2) (b:=t+ε/2) _ ⟨by linarith,by linarith⟩ x
  intro r hr
  apply hεJ
  rw [mem_ball,Real.dist_eq,abs_lt]
  constructor <;> linarith [hr.1,hr.2]

lemma space_time_derivative_slab {T : ℝ} (hT : 0<T)
    (hF : SpatialJetRegular 0 (Icc 0 T) F) (hG : SpatialJetRegular 0 (Icc 0 T) G)
    (htime : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t)
    {t : ℝ} (ht : t∈Icc 0 T) (x : U) :
    HasDerivWithinAt (fun r => fderiv ℝ (fun y => F (r,y)) x)
      (fderiv ℝ (fun y => G (t,y)) x) (Icc 0 T) t := by
  let DF := fun r => fderiv ℝ (fun y => F (r,y)) x
  let DG := fun r => fderiv ℝ (fun y => G (r,y)) x
  have hcG (y : U) : ContinuousOn (fun r => G (r,y)) (Icc 0 T) :=
    hG.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have hcF (y : U) : ContinuousOn (fun r => F (r,y)) (Icc 0 T) :=
    hF.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have hcDG : ContinuousOn DG (Icc 0 T) :=
    hG.deriv.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have he (r : ℝ) (hr : r∈Icc 0 T) : DF r = DF 0+∫ u in 0..r, DG u := by
    have hsub : Icc 0 r ⊆ Icc 0 T := Icc_subset_Icc_right hr.2
    have hgi (y : U) : IntervalIntegrable (fun u => G (u,y)) volume 0 r :=
      ContinuousOn.intervalIntegrable_of_Icc hr.1 ((hcG y).mono hsub)
    have heq : (fun y => ∫ u in 0..r, G (u,y)) = (fun y => F (r,y)-F (0,y)) := by
      funext y
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 ((hcF y).mono hsub) _ (hgi y)
      intro u hu
      exact (htime u ⟨hu.1.le,hu.2.le.trans hr.2⟩ y).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le hr.2))
    have hd := hG.hasFDerivAt_timeIntegral hr.1 hsub x
    rw [heq] at hd
    have hdf := (((hF.1 r hr).differentiable (by simp) x).hasFDerivAt.sub
      (((hF.1 0 ⟨le_rfl,hT.le⟩).differentiable (by simp) x).hasFDerivAt))
    have hh := hd.unique hdf
    change (∫ u in 0..r, DG u)=DF r-DF 0 at hh
    rw [hh]
    abel
  have hgi : IntervalIntegrable DG volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hcDG.mono (Icc_subset_Icc_right ht.2))
  let : Fact (t∈Icc (0:ℝ) T) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s:=Icc 0 T) (t:=Icc 0 T) hgi
    (hcDG.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hcDG t ht)
  exact (hd.const_add (DF 0)).congr he (he t ht)

end RVM

end

end OAI
