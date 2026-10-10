import OAI.Geometry.Relativity.CKS.SourceReplacement
import OAI.Geometry.Relativity.CKS.TransferDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold
open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior
open scoped ContDiff Topology
namespace CKSMain
universe u
attribute [local instance] manifold_regular
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H3 N] [IsManifold I3 ∞ N]

def restrictConstraintChart
    {q q' : SmoothMetric I3 (M := N)} {k k' : InnerField I3 (M := N)}
    {x : N} (c : ConstraintChart q.inner k x)
    {V : Set N} (ho : IsOpen V) (hx : x ∈ V)
    (he : ∀ y ∈ V, q'.inner y = q.inner y ∧ k' y = k y) :
    ConstraintChart q'.inner k' x where
  domain := c.domain ∩ V
  coordinate := c.coordinate
  metric := c.metric
  tensor := c.tensor
  isOpen := c.isOpen.inter ho
  mem := ⟨c.mem,hx⟩
  smooth := c.smooth.mono inter_subset_left
  fullRank y hy := c.fullRank y hy.1
  coefficientSmooth y hy := c.coefficientSmooth y hy.1
  positiveSymmetric y hy := c.positiveSymmetric y hy.1
  represents y hy := by rw [(he y hy.2).1,(he y hy.2).2]; exact c.represents y hy.1

def BoundaryGeometry.transfer
    {q q' : SmoothMetric I3 (M := N)} {k k' : InnerField I3 (M := N)}
    (B : BoundaryGeometry q k) {V : Set N} (ho : IsOpen V)
    (hs : I3.boundary N ⊆ V)
    (he : ∀ y ∈ V, q'.inner y = q.inner y ∧ k' y = k y) :
    BoundaryGeometry q' k' where
  normal := B.normal
  unit p := by rw [(he p.val (hs p.property)).1]; exact B.unit p
  orthogonal p a := by rw [(he p.val (hs p.property)).1]; exact B.orthogonal p a
  inward := B.inward
  chart p := restrictConstraintChart (B.chart p) ho (hs p.property) he
  normal_smooth := B.normal_smooth

lemma weakBoundary_of_marginal_near
    {q q' : SmoothMetric I3 (M := N)} {k k' : InnerField I3 (M := N)}
    (h : MarginalBoundary q k) {V : Set N} (ho : IsOpen V)
    (hs : I3.boundary N ⊆ V)
    (he : ∀ y ∈ V, q'.inner y = q.inner y ∧ k' y = k y) :
    WeakFutureBoundary q' k' := by
  obtain ⟨B,hB⟩ := h
  exact ⟨B.transfer ho hs he,fun p => (hB p).le⟩

omit [IsManifold I3 ∞ N] in
lemma compact_boundary_neighbourhood [IsManifold I3 ∞ N] (c : CoordinateEnd (N := N))
    (hS : IsCompact (I3.boundary N)) :
    ∃ (r : ℝ) (V : Set N), IsOpen V ∧ I3.boundary N ⊆ V ∧
      ∀ R ≥ r, ∀ x ∈ V, x ∉ c.domain ∨ ‖c.coordinate x‖ ≤ R := by
  obtain ⟨s,hs,h⟩ := compact_side_eventually c.coordinate c.closed_far_side hS
  refine ⟨s+1,{x : N | x ∈ c.domain ∧ s+1 ≤ ‖c.coordinate x‖}ᶜ,
    (c.closed_far_side (s+1) (by linarith)).isOpen_compl,?_,?_⟩
  · intro x hx hh
    rcases h s le_rfl x hx with hn | hn
    · exact hn hh.1
    · linarith [hh.2]
  · intro R hR x hx
    by_cases hd : x ∈ c.domain
    · right
      have hn : ‖c.coordinate x‖ < s+1 := lt_of_not_ge (fun hn => hx ⟨hd,hn⟩)
      exact hn.le.trans hR
    · exact Or.inl hd

lemma tail_zero_symbol {L : SpatialTensor} {r : ℝ}
    (h : ∀ x : CKSLorentz.E, r < ‖x‖ → L x = 0) (i j : Fin 3) :
    CKSADM.SymbolN 1 (1+(1:ℝ)) (fun x => spatialCartesian L x i j) := by
  apply (CKSADM.SymbolN.zero 1 (1+(1:ℝ))).congr
  filter_upwards [CKSADM.eventually_norm_gt r] with x hx
  simp [spatialCartesian,spatialCoefficients,h x hx]

lemma bondiMass_pos {g : SmoothMetric I3 (M := N)} {K : InnerField I3 (M := N)}
    (d : CKSData g K) (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1) :
    0 < bondiMass d := by
  apply Real.sqrt_pos.mpr
  have h0 := norm_nonneg (bondiCharge d.massAspect).2
  nlinarith

theorem transfer_inequality [T2Space N] [SecondCountableTopology N] [ConnectedSpace N]
    (hAF : WeakAFExteriorInequality.{u})
    (g : SmoothMetric I3 (M := N)) (K : InnerField I3 (M := N))
    (hK : ContMDiff I3 (I3.prod 𝓘(ℝ,SpatialBilinear)) ∞ (innerSection I3 K))
    (hKsym : ∀ x v w, K x v w = K x w v)
    (hOrient : Orientable (N := N))
    (hScompact : IsCompact (I3.boundary N)) (hSnonempty : (I3.boundary N).Nonempty)
    (hcomplete : CKSReplacementCompleteness.IsComplete I3 g.toContinuousRiemannianMetric)
    (hDEC : PhysicalDEC I3 g.inner K) (d : CKSData g K)
    (ht : ‖(bondiCharge d.massAspect).2‖ < (bondiCharge d.massAspect).1)
    (hboundary : MarginalBoundary g K) :
    Real.sqrt (minimumEnclosingArea g / (16*Real.pi)) ≤ bondiMass d := by
  obtain ⟨d',R₀,ε,hcharge,hR₀,h12,hε,hfinite,hout⟩ :=
    area_controlled_end_replacement g K hK hKsym hOrient hScompact hSnonempty hcomplete hDEC d ht
  obtain ⟨s,V,hVo,hVS,hV⟩ := compact_boundary_neighbourhood d'.chart hScompact
  have hm := bondiMass_pos d ht
  have hn : ∀ᶠ R : ℝ in atTop,
      Real.sqrt (((1-ε R)*minimumEnclosingArea g)/(16*Real.pi)) ≤
        bondiMass d + 2*R^(-(1/2:ℝ)) := by
    filter_upwards [eventually_ge_atTop (max R₀ s)] with R hR
    obtain ⟨heps,gR,kR,G,L,η,hkR,hksym,hold,hDECR,hlower,hcompleteR,hint,hrep,hAFtail,
      hzero,hE,hP,hη0,hηbound,hfinR,harea,hcuts⟩ := hout R ((le_max_left _ _).trans hR)
    have hBR : WeakFutureBoundary gR kR :=
      weakBoundary_of_marginal_near hboundary hVo hVS
        (fun x hx => hold x (hV R ((le_max_right _ _).trans hR) x hx))
    have hηpos : 0 < bondiMass d + η := add_pos_of_pos_of_nonneg hm hη0
    have hineq := hAF N gR kR hkR hksym hOrient hScompact hSnonempty hcompleteR
      d'.chart G L 1 (bondiMass d + η) 0 hrep (by norm_num)
      (fun i j => (hAFtail i j).2 2) (tail_zero_symbol hzero) hDECR hint hE hP
      (by simpa using hηpos) hBR
    have hmass : Real.sqrt ((bondiMass d + η)^2 -
        ‖(WithLp.toLp 2 (0 : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3))‖^2) = bondiMass d + η := by
      simpa using Real.sqrt_sq hηpos.le
    rw [hmass] at hineq
    calc
      Real.sqrt (((1-ε R)*minimumEnclosingArea g)/(16*Real.pi)) ≤
          Real.sqrt (minimumEnclosingArea gR/(16*Real.pi)) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_right harea (by positivity))
      _ ≤ bondiMass d + η := hineq
      _ ≤ bondiMass d + 2*R^(-(1/2:ℝ)) := add_le_add le_rfl hηbound
  have hleft : Tendsto (fun R => Real.sqrt (((1-ε R)*minimumEnclosingArea g)/(16*Real.pi)))
      atTop (𝓝 (Real.sqrt (minimumEnclosingArea g/(16*Real.pi)))) := by
    convert (((tendsto_const_nhds.sub hε).mul_const (minimumEnclosingArea g)).div_const
      (16*Real.pi)).sqrt using 1
    simp
  have hright : Tendsto (fun R : ℝ => bondiMass d + 2*R^(-(1/2:ℝ)))
      atTop (𝓝 (bondiMass d)) := by
    have hpow := tendsto_rpow_neg_atTop (y := (1/2:ℝ)) (by norm_num : (0:ℝ)<1/2)
    convert tendsto_const_nhds.add (hpow.const_mul 2) using 1
    simp
  exact le_of_tendsto_of_tendsto hleft hright hn
end CKSMain

end

end OAI
