import OAI.Geometry.KahlerSplitting.CommutingFlows

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
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Metric Filter Topology
open Set Filter Topology Metric
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_normalized_projection_lift {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    {p : E} (hp : p ∈ U) (L : F →L[ℂ] E) (Q : E →L[ℂ] F)
    (hQL : Q.comp L = ContinuousLinearMap.id ℂ F) (hLQ : L.comp Q = P p) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ W : E → F →L[ℂ] E, DifferentiableOn ℂ W O ∧ W p = L ∧
        ∀ x ∈ O,
          (∀ v, P x (W x v) = W x v) ∧
          (∀ v, Q (W x v) = v) ∧
          (∀ v, P x v = v → W x (Q v) = v) := by
  let A : E → F →L[ℂ] F := fun x ↦ Q.comp ((P x).comp L)
  have hQLe (v : F) : Q (L v) = v := by
    simpa using congrArg (fun B : F →L[ℂ] F ↦ B v) hQL
  have hLQe (v : E) : L (Q v) = P p v := by
    simpa using congrArg (fun B : E →L[ℂ] E ↦ B v) hLQ
  have hPL (v : F) : P p (L v) = L v := by rw [← hLQe,hQLe]
  have hAp : A p = ContinuousLinearMap.id ℂ F := by
    ext v
    change Q (P p (L v)) = v
    rw [hPL,hQLe]
  have hA : DifferentiableOn ℂ A U :=
    (differentiableOn_const Q).clm_comp (hP.clm_comp (differentiableOn_const L))
  have hAc := hA.differentiableAt (hU.mem_nhds hp)
  have hAn : ∀ᶠ x in 𝓝 p, IsUnit (A x) := by
    have hn : {B : F →L[ℂ] F | IsUnit B} ∈ 𝓝 (A p) := by
      rw [hAp]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hAc.continuousAt.tendsto.eventually hn
  have hPn : ∀ᶠ x in 𝓝 p, ‖P x - P p‖ < 1 := by
    apply ((hP.differentiableAt (hU.mem_nhds hp)).continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
    simp
  have hn : U ∩ {x | IsUnit (A x) ∧ ‖P x - P p‖ < 1} ∈ 𝓝 p :=
    inter_mem (hU.mem_nhds hp) (hAn.and hPn)
  obtain ⟨O,hO,hOo,hOp⟩ := _root_.mem_nhds_iff.mp hn
  have hOU : O ⊆ U := fun x hx ↦ (hO hx).1
  have hInv (x : E) (hx : x ∈ O) : (A x).IsInvertible := by
    obtain ⟨u,hu⟩ := (hO hx).2.1
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℂ F u,hu⟩
  let W : E → F →L[ℂ] E := fun x ↦ (P x).comp (L.comp (A x).inverse)
  have hAi : DifferentiableOn ℂ (fun x ↦ (A x).inverse) O := by
    intro x hx
    have hInvD := ((hInv x hx).contDiffAt_map_inverse (n := (1 : ℕ∞ω))).differentiableAt (by norm_num)
    exact (hInvD.comp x (hA.differentiableAt (hU.mem_nhds (hOU hx)))).differentiableWithinAt
  have hW : DifferentiableOn ℂ W O :=
    (hP.mono hOU).clm_comp ((differentiableOn_const L).clm_comp hAi)
  have hWp : W p = L := by
    ext v
    simp [W,hAp,hPL]
  refine ⟨O,hOo,hOp,hOU,W,hW,hWp,?_⟩
  intro x hx
  have hWrange (v : F) : P x (W x v) = W x v := hid x (hOU hx) _
  have hQW (v : F) : Q (W x v) = v := (hInv x hx).self_apply_inverse v
  have hinj (v : E) (hv : P x v = v) (hq : Q v = 0) : v = 0 := by
    have hpv : P p v = 0 := by rw [← hLQe,hq,map_zero]
    have hd : (P x - P p) v = v := by simp [hv,hpv]
    have hle := (P x - P p).le_opNorm v
    rw [hd] at hle
    have hs := (hO hx).2.2
    by_contra hv0
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    nlinarith
  refine ⟨hWrange,hQW,?_⟩
  intro v hv
  apply sub_eq_zero.mp
  apply hinj
  · rw [map_sub,hWrange,hv]
  · rw [map_sub,hQW,sub_self]

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def InvolutiveProjectionOn (P : E → E →L[ℂ] E) (U : Set E) : Prop :=
  ∀ V W : E → E, DifferentiableOn ℂ V U → DifferentiableOn ℂ W U →
    (∀ x ∈ U, P x (V x) = V x) → (∀ x ∈ U, P x (W x) = W x) →
    ∀ x ∈ U, P x (VectorField.lieBracket ℂ V W x) = VectorField.lieBracket ℂ V W x

theorem normalized_lift_commutes {U : Set E} (hU : IsOpen U)
    {P : E → E →L[ℂ] E} (hInt : InvolutiveProjectionOn P U)
    (Q : E →L[ℂ] F) (W : E → F →L[ℂ] E) (hW : DifferentiableOn ℂ W U)
    (hrange : ∀ x ∈ U, ∀ v, P x (W x v) = W x v)
    (hQW : ∀ x ∈ U, ∀ v, Q (W x v) = v)
    (hRet : ∀ x ∈ U, ∀ v, P x v = v → W x (Q v) = v)
    (v w : F) {x : E} (hx : x ∈ U) :
    fderiv ℂ (fun y ↦ W y w) x (W x v) =
      fderiv ℂ (fun y ↦ W y v) x (W x w) := by
  have hd (u : F) : DifferentiableOn ℂ (fun y ↦ W y u) U :=
    hW.clm_apply (differentiableOn_const u)
  have hzero (u : F) : Q.comp (fderiv ℂ (fun y ↦ W y u) x) = 0 := by
    have hdu := (hd u).differentiableAt (hU.mem_nhds hx)
    have hc := Q.hasFDerivAt.comp x hdu.hasFDerivAt
    have hh : HasFDerivAt (fun y ↦ Q (W y u)) (0 : E →L[ℂ] F) x := by
      apply (hasFDerivAt_const u x).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hQW y hy u
    exact hc.unique hh
  have hb := hInt (fun y ↦ W y v) (fun y ↦ W y w) (hd v) (hd w)
    (fun y hy ↦ hrange y hy v) (fun y hy ↦ hrange y hy w) x hx
  have hQb : Q (VectorField.lieBracket ℂ (fun y ↦ W y v) (fun y ↦ W y w) x) = 0 := by
    have hv := congrArg (fun L : E →L[ℂ] F ↦ L (W x w)) (hzero v)
    have hw := congrArg (fun L : E →L[ℂ] F ↦ L (W x v)) (hzero w)
    change Q (fderiv ℂ (fun y ↦ W y v) x (W x w)) = 0 at hv
    change Q (fderiv ℂ (fun y ↦ W y w) x (W x v)) = 0 at hw
    simp only [VectorField.lieBracket,map_sub,hv,hw,sub_self]
  have h := hRet x hx _ hb
  rw [hQb,map_zero] at h
  exact sub_eq_zero.mp h.symm

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_normalized_commuting_frame {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    {p : E} (hp : p ∈ U) (n : ℕ) (L : (Fin n → ℂ) →L[ℂ] E)
    (Q : E →L[ℂ] (Fin n → ℂ))
    (hQL : Q.comp L = ContinuousLinearMap.id ℂ (Fin n → ℂ)) (hLQ : L.comp Q = P p) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ W : E → (Fin n → ℂ) →L[ℂ] E,
      ∃ V : Fin n → C(E,E), ∃ D : Fin n → C(E,E →L[ℂ] E),
        W p = L ∧
        (∀ x ∈ O, (∀ v, P x (W x v) = W x v) ∧
          (∀ v, Q (W x v) = v) ∧ (∀ v, P x v = v → W x (Q v) = v)) ∧
        (∀ i x, x ∈ O → V i x = W x (Pi.single i 1) ∧ HasFDerivAt (V i) (D i x) x) ∧
        (∀ i j x, x ∈ O → D j x (V i x) = D i x (V j x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨N,hNo,hNp,hNU,W,hW,hWp,hWN⟩ :=
    exists_normalized_projection_lift hU P hP hid hp L Q hQL hLQ
  let F : Fin n → E → E := fun i x ↦ W x (Pi.single i 1)
  have hF (i : Fin n) : DifferentiableOn ℂ (F i) N :=
    hW.clm_apply (differentiableOn_const (Pi.single i 1))
  obtain ⟨O,hOo,hOp,hON,V,D,hrep⟩ := finite_holomorphic_representatives hNo F hF hNp
  refine ⟨O,hOo,hOp,hON.trans hNU,W,V,D,hWp,fun x hx ↦ hWN x (hON hx),?_,?_⟩
  · intro i x hx
    exact ⟨(hrep i x hx).1,(hrep i x hx).2.2⟩
  · intro i j x hx
    rw [(hrep j x hx).2.1,(hrep i x hx).2.1,(hrep i x hx).1,(hrep j x hx).1]
    exact normalized_lift_commutes hNo (hInt N hNo hNU) Q W hW
      (fun x hx ↦ (hWN x hx).1) (fun x hx ↦ (hWN x hx).2.1)
      (fun x hx ↦ (hWN x hx).2.2) (Pi.single i 1) (Pi.single j 1) (hON hx)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace CommutingFlowData
variable {n : ℕ} {V : Fin n → C(E,E)} {D : Fin n → C(E,E →L[ℂ] E)}
  {U : Set E} {p : E} (G : CommutingFlowData n V D U p)

theorem fderiv_initial_zero {x : E} (hx : (x,0) ∈ G.domain) (u : E) :
    fderiv ℂ G.map (x,0) (u,0) = u := by
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hx)).differentiableAt (by norm_num)
  let emb : E →L[ℂ] E × FlowTimes n :=
    (ContinuousLinearMap.id ℂ E).prod 0
  have he : HasFDerivAt (fun y ↦ G.map (y,0))
      ((fderiv ℂ G.map (x,0)).comp emb) x := hG.hasFDerivAt.comp x emb.hasFDerivAt
  have hz : (fun y ↦ G.map (y,0)) =ᶠ[𝓝 x] (fun y ↦ y) := by
    have hn := emb.continuous.continuousAt.tendsto.eventually
      (G.isOpen_domain.mem_nhds hx)
    filter_upwards [hn] with y hy
    exact G.zero y hy
  have hid := (hasFDerivAt_id (𝕜 := ℂ) x).congr_of_eventuallyEq hz
  have heq := congrArg (fun A : E →L[ℂ] E ↦ A u) (he.unique hid)
  exact heq

theorem fderiv_time_sum {q : E × FlowTimes n} (hq : q ∈ G.domain) (t : FlowTimes n) :
    fderiv ℂ G.map q (0,t) = ∑ i, t i • V i (G.map q) := by
  let A : FlowTimes n →L[ℂ] E := (fderiv ℂ G.map q).comp
    ((0 : FlowTimes n →L[ℂ] E).prod (ContinuousLinearMap.id ℂ (FlowTimes n)))
  have h := congrArg A (pi_eq_sum_univ' t)
  simpa only [A,map_sum,map_smul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,G.time q hq] using h

theorem fderiv_base (u : E) (t : FlowTimes n) :
    fderiv ℂ G.map (p,0) (u,t) = u + ∑ i, t i • V i p := by
  have hsplit : (u,t) = (u,0) + (0,t) := by simp
  rw [hsplit,map_add,G.fderiv_initial_zero G.base_mem,
    G.fderiv_time_sum G.base_mem,G.zero p G.base_mem]

end CommutingFlowData

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem transverse_flow_hasFDerivAt {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (hV : ∀ i, V i p = L (Pi.single i 1,0)) :
    HasFDerivAt (fun q : FlowTimes n × C ↦ G.map (p+L (0,q.2),q.1))
      (L : (FlowTimes n × C) →L[ℂ] E) 0 := by
  let B : (FlowTimes n × C) →L[ℂ] E × FlowTimes n :=
    ((L : (FlowTimes n × C) →L[ℂ] E).comp
      ((0 : (FlowTimes n × C) →L[ℂ] FlowTimes n).prod (ContinuousLinearMap.snd ℂ _ _))).prod
      (ContinuousLinearMap.fst ℂ _ _)
  have hB : HasFDerivAt (fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) B 0 := by
    convert! B.hasFDerivAt.const_add (p,0) using 1
    ext q <;> simp [B]
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds G.base_mem)).differentiableAt (by norm_num)
  have hG' : HasFDerivAt G.map (fderiv ℂ G.map (p,0))
      ((fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) 0) := by
    change HasFDerivAt G.map (fderiv ℂ G.map (p,0)) (p+L (0 : FlowTimes n × C),0)
    simpa only [map_zero,add_zero] using hG.hasFDerivAt
  have hc := hG'.comp (f := fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) 0 hB
  convert! hc using 1
  apply ContinuousLinearMap.ext
  intro q
  change L q = fderiv ℂ G.map (p,0) (L (0,q.2),q.1)
  rw [G.fderiv_base]
  simp_rw [hV,← map_smul]
  rw [← map_sum,← map_add]
  congr 1
  let J : FlowTimes n →L[ℂ] FlowTimes n × C :=
    (ContinuousLinearMap.id ℂ (FlowTimes n)).prod 0
  have hs := congrArg J (pi_eq_sum_univ' q.1)
  simp only [map_sum,map_smul,J,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] at hs
  rw [← hs]
  simp

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

abbrev transverseFlowParameter {n : ℕ} (p : E) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (q : FlowTimes n × C) : E × FlowTimes n := (p+L (0,q.2),q.1)

def transverseFlowLinear {n : ℕ} (L : (FlowTimes n × C) ≃L[ℂ] E) :
    (FlowTimes n × C) →L[ℂ] E × FlowTimes n :=
  ((L : (FlowTimes n × C) →L[ℂ] E).comp
    ((0 : (FlowTimes n × C) →L[ℂ] FlowTimes n).prod (ContinuousLinearMap.snd ℂ _ _))).prod
    (ContinuousLinearMap.fst ℂ _ _)

theorem transverseFlowParameter_hasFDerivAt {n : ℕ} (p : E)
    (L : (FlowTimes n × C) ≃L[ℂ] E) (q : FlowTimes n × C) :
    HasFDerivAt (transverseFlowParameter p L) (transverseFlowLinear L) q := by
  convert! (transverseFlowLinear L).hasFDerivAt.const_add (p,0) using 1
  ext z <;> simp [transverseFlowLinear]

theorem transverseFlow_time {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    {q : FlowTimes n × C} (hq : transverseFlowParameter p L q ∈ G.domain)
    (t : FlowTimes n) :
    fderiv ℂ (G.map ∘ transverseFlowParameter p L) q (t,0) =
      ∑ i, t i • V i (G.map (transverseFlowParameter p L q)) := by
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hq)).differentiableAt (by norm_num)
  have hd := (hG.hasFDerivAt.comp q (transverseFlowParameter_hasFDerivAt p L q)).fderiv
  rw [hd]
  change fderiv ℂ G.map (transverseFlowParameter p L q) (L (0,0),t) = _
  have hL0 : L (0,(0 : C)) = 0 := map_zero L
  rw [hL0,G.fderiv_time_sum hq]

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_holomorphic_ift_chart {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : ContDiffOn ℂ 1 f U) {p : E} (hp : p ∈ U)
    (L : E ≃L[ℂ] F) (hL : HasFDerivAt f (L : E →L[ℂ] F) p) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ p ∈ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target := by
  have hc := hf.contDiffAt (hU.mem_nhds hp)
  have hn : (1 : ℕ∞ω) ≠ 0 := by norm_num
  let e := hc.toOpenPartialHomeomorph f hL hn
  have hpe : p ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hL hn
  have hi : ContDiffAt ℂ 1 e.symm (f p) := hc.to_localInverse hL hn
  obtain ⟨R,hR,hRi⟩ := hi.contDiffOn le_rfl (by norm_num)
  obtain ⟨O,hOR,hOo,hOp⟩ := _root_.mem_nhds_iff.mp hR
  let S := U ∩ f ⁻¹' O
  have hS : IsOpen S := hf.continuousOn.isOpen_inter_preimage hU hOo
  let g := e.restrOpen S hS
  have hgf : (g : E → F) = f := rfl
  have hGU : g.source ⊆ U := fun x hx ↦ hx.2.1
  refine ⟨g,hgf,⟨hpe,hp,hOp⟩,hGU,?_,?_⟩
  · rw [hgf]
    exact hf.mono hGU
  · intro y hy
    have hx := g.map_target hy
    have hfy : f (g.symm y) = y := g.right_inv hy
    have hyO : y ∈ O := hfy ▸ hx.2.2
    exact (hRi y (hOR hyO)).mono (fun z hz ↦ by
      have hz' := g.map_target hz
      have heq : f (g.symm z) = z := g.right_inv hz
      exact hOR (heq ▸ hz'.2.2))

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E F C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem chart_fderiv_inverse (e : OpenPartialHomeomorph F E)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    {x : F} (hx : x ∈ e.source) (v : F) (w : E) :
    fderiv ℂ e.symm (e x) (fderiv ℂ e x v) = v ∧
      fderiv ℂ e x (fderiv ℂ e.symm (e x) w) = w := by
  have hd := he.differentiableAt (e.open_source.mem_nhds hx)
  have hdi := hi.differentiableAt (e.open_target.mem_nhds (e.map_source hx))
  have hleft : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hright : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have hcl := hdi.hasFDerivAt.comp x hd.hasFDerivAt
  have hdr : HasFDerivAt e (fderiv ℂ e x) (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hd.hasFDerivAt
  have hcr := hdr.comp (f := e.symm) (e x) hdi.hasFDerivAt
  have hl := hcl.unique ((hasFDerivAt_id (𝕜 := ℂ) x).congr_of_eventuallyEq hleft)
  have hr := hcr.unique ((hasFDerivAt_id (𝕜 := ℂ) (e x)).congr_of_eventuallyEq hright)
  exact ⟨congrArg (fun A : F →L[ℂ] F ↦ A v) hl,
    congrArg (fun A : E →L[ℂ] E ↦ A w) hr⟩

theorem chart_kernel_eq_projection
    (e : OpenPartialHomeomorph (F × C) E)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (P : E → E →L[ℂ] E) (W : E → F →L[ℂ] E) (Q : E →L[ℂ] F)
    (hframe : ∀ q ∈ e.source, ∀ t, fderiv ℂ e q (t,0) = W (e q) t)
    (hrange : ∀ y ∈ e.target, ∀ t, P y (W y t) = W y t)
    (hret : ∀ y ∈ e.target, ∀ v, P y v = v → W y (Q v) = v)
    {y : E} (hy : y ∈ e.target) (v : E) :
    P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let q := e.symm y
  have hq : q ∈ e.source := e.map_target hy
  have heq : e q = y := e.right_inv hy
  constructor
  · intro hv
    have hw : fderiv ℂ e q (Q v,0) = v := by
      rw [hframe q hq,heq,hret y hy v hv]
    have hl := (chart_fderiv_inverse e he hi hq (Q v,0) v).1
    rw [heq,hw] at hl
    exact congrArg Prod.snd hl
  · intro hv
    have hr := (chart_fderiv_inverse e he hi hq (0,0) v).2
    rw [heq] at hr
    have ht : fderiv ℂ e.symm y v = ((fderiv ℂ e.symm y v).1,0) := by
      exact Prod.ext rfl hv
    rw [ht,hframe q hq,heq] at hr
    rw [← hr]
    exact hrange y hy _

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]

theorem foliation_chart_from_flows {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (hV0 : ∀ i, V i p = L (Pi.single i 1,0))
    (P : E → E →L[ℂ] E) (W : E → FlowTimes n →L[ℂ] E) (Q : E →L[ℂ] FlowTimes n)
    (hVW : ∀ i x, x ∈ U → V i x = W x (Pi.single i 1))
    (hrange : ∀ x ∈ U, ∀ t, P x (W x t) = W x t)
    (hret : ∀ x ∈ U, ∀ v, P x v = v → W x (Q v) = v) :
    ∃ e : OpenPartialHomeomorph (FlowTimes n × C) E,
      (0 : FlowTimes n × C) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let η := transverseFlowParameter p L
  have hη : ContDiff ℂ 1 η := by
    exact (contDiff_const.add (L.contDiff.comp (contDiff_const.prodMk contDiff_snd))).prodMk contDiff_fst
  let O := η ⁻¹' G.domain
  have hO : IsOpen O := G.isOpen_domain.preimage hη.continuous
  have hL0 : L (0,(0 : C)) = 0 := map_zero L
  have h0 : (0 : FlowTimes n × C) ∈ O := by
    simpa only [O,mem_preimage,η,transverseFlowParameter,Prod.fst_zero,Prod.snd_zero,
      hL0,add_zero] using G.base_mem
  let f : FlowTimes n × C → E := G.map ∘ η
  have hf : ContDiffOn ℂ 1 f O := G.contDiff.comp hη.contDiffOn (fun _ hq ↦ hq)
  have hd : HasFDerivAt f (L : (FlowTimes n × C) →L[ℂ] E) 0 :=
    transverse_flow_hasFDerivAt G L hV0
  obtain ⟨e,he,hep,heO,hee,hei⟩ := exists_holomorphic_ift_chart hO hf h0 L hd
  have htarget : e.target ⊆ U := by
    intro y hy
    have hx := e.map_target hy
    have hr := G.mapsTo (heO hx)
    change f (e.symm y) ∈ U at hr
    rw [← he,e.right_inv hy] at hr
    exact hr
  have htime (q : FlowTimes n × C) (hq : q ∈ e.source) (t : FlowTimes n) :
      fderiv ℂ e q (t,0) = W (e q) t := by
    rw [he]
    have ht := transverseFlow_time G L (heO hq) t
    change fderiv ℂ f q (t,0) = _ at ht
    rw [ht]
    calc
      (∑ i, t i • V i (f q)) = ∑ i, t i • W (f q) (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hVW i (f q) (G.mapsTo (heO hq))]
      _ = W (f q) t := by
        simpa only [map_sum,map_smul] using (congrArg (W (f q)) (pi_eq_sum_univ' t)).symm
  refine ⟨e,hep,?_,htarget,hee,hei,?_⟩
  · rw [he]
    change G.map (p+L (0,0),0) = p
    rw [hL0,add_zero]
    exact G.zero p G.base_mem
  · intro y hy v
    exact chart_kernel_eq_projection e (hee.differentiableOn (by norm_num))
      (hei.differentiableOn (by norm_num)) P W Q htime
      (fun x hx ↦ hrange x (htarget hx)) (fun x hx ↦ hret x (htarget hx)) hy v

end UniversalCoverSplitting

open Set

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_projection_coordinates (P : E →L[ℂ] E)
    (hid : ∀ v, P (P v) = P v) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range P.toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker P.toLinearMap) = s) :
    ∃ L : ((Fin r → ℂ) × (Fin s → ℂ)) ≃L[ℂ] E,
      ∀ v, L ((L.symm v).1,0) = P v := by
  have hP : IsIdempotentElem P.toLinearMap := by
    ext v
    exact hid v
  let R := LinearMap.range P.toLinearMap
  let K := LinearMap.ker P.toLinearMap
  let a : R ≃ₗ[ℂ] (Fin r → ℂ) := (Module.finBasisOfFinrankEq ℂ R hr).equivFun
  let b : K ≃ₗ[ℂ] (Fin s → ℂ) := (Module.finBasisOfFinrankEq ℂ K hs).equivFun
  let e : (R × K) ≃ₗ[ℂ] E := Submodule.prodEquivOfIsCompl R K (LinearMap.IsIdempotentElem.isCompl hP)
  let L := ((a.symm.prodCongr b.symm).trans e).toContinuousLinearEquiv
  refine ⟨L,?_⟩
  intro v
  obtain ⟨q,rfl⟩ := L.surjective v
  rw [L.symm_apply_apply]
  have hR : P (a.symm q.1) = a.symm q.1 := (LinearMap.IsIdempotentElem.mem_range_iff hP).mp (a.symm q.1).property
  have hK : P (b.symm q.2) = 0 := (b.symm q.2).property
  change ((a.symm q.1 : R) : E) + ((b.symm 0 : K) : E) =
    P (((a.symm q.1 : R) : E) + ((b.symm q.2 : K) : E))
  simp only [map_zero,Submodule.coe_zero,map_add,hR,hK,add_zero]

end UniversalCoverSplitting

end

end OAI
