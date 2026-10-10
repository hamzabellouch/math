import OAI.Probability.DilutedSpin.RegularNodeProducer

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance regularNodeAverageDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p : ℕ}

/-- Regular depth-cube average of the literal physical covariance energy. -/
noncomputable def physicalShapeAverage (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  DepthAverage.average (regularShapeDomain S (L+1) η)
    (physicalScheduledEnergy M θB hB N L u S)

lemma physicalShapeAverage_nonneg (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalShapeAverage M θB hB N L u S η :=
  DepthAverage.average_nonneg _ _ (physicalScheduledEnergy_nonneg M θB hB N L u S)

lemma physicalShapeAverage_le_one (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalShapeAverage M θB hB N L u S η≤1 :=
  DepthAverage.average_le_const _ _ zero_le_one
    (fun Q _ => physicalScheduledEnergy_le_one M θB hB N L u S Q)

noncomputable def physicalChildrenAverage (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (C : Fin k → ReducedTopology) (η : ℝ) : ℝ :=
  Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (physicalShapeAverage M θB hB N L u (C j) (η/2)))

lemma averaged_multileaf_scalar_bound {α : Type} [Fintype α] [DecidableEq α]
    {L : ℕ} [NeZero L] (D : (α → Fin L) → Prop)
    (F E W W' H : (α → Fin L) → ℝ) {η δ K P k B B' : ℝ}
    (hδ : 0≤δ) (hK : 0≤K) (hP : 0≤P) (hk : 0≤k)
    (hpoint : ∀ Q, D Q → η*F Q≤4*δ+2*E Q+4*K*W' Q+2*K*H Q+(4*P+16*k)*W Q)
    (hW : DepthAverage.average D W≤B) (hW' : DepthAverage.average D W'≤B)
    (hH : DepthAverage.average D H≤B') :
    η*DepthAverage.average D F≤4*δ+2*DepthAverage.average D E+(4*K+4*P+16*k)*B+2*K*B' := by
  have hav := DepthAverage.average_mono D _ _ hpoint
  simp only [DepthAverage.average_add_eq,DepthAverage.average_const_mul] at hav
  have hd : DepthAverage.average D (fun _ => δ)≤δ :=
    DepthAverage.average_le_const _ _ hδ (fun _ _ => le_rfl)
  have hc₀ := mul_le_mul_of_nonneg_left hW (by positivity : 0≤4*P+16*k)
  have hc₁ := mul_le_mul_of_nonneg_left hW' (by positivity : 0≤4*K)
  have hs := mul_le_mul_of_nonneg_left hH (by positivity : 0≤2*K)
  linarith only [hav,hd,hc₀,hc₁,hs]

lemma physicalChildMass_average (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) (s : Bool) :
    DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η)
      (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C s Q))≤
      physicalChildrenAverage M θB hB N L u k C η :=
  physical_scheduled_child_moment M θB hB N L u hη hlarge k hk C s

lemma regular_node_average_inequality (M : Model p) (θB hB : ℝ) (N L : ℕ)
    (u : Spec L × ℕ → ℝ) (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ))
    (S T : (Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → PrescribedTree (L+1))
    (a : (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → (S Q).Leaf)
    (q : (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) →
      Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → (T Q).Leaf)
    (J : (Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) → ℝ)
    (hpoint : ∀ Q, regularShapeDomain (.node k hk C) (L+1) η Q →
      η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
        4*((L+1:ℕ):ℝ)⁻¹ +
        2*(|physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
        4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
        2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
        (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
          Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q)) :
    η*physicalShapeAverage M θB hB N L u (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η) (fun Q =>
        |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        physicalChildrenAverage M θB hB N L u k C η +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) := by
  have hc (s : Bool) := physicalChildMass_average M θB hB N L u k hk C hη hlarge s
  have hs := physicalNodeShift_average M θB hB N L u k hk C η (by linarith)
  have hb := averaged_multileaf_scalar_bound
    (regularShapeDomain (.node k hk C) (L+1) η)
    (physicalScheduledEnergy M θB hB N L u (.node k hk C))
    (fun Q => |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|)
    (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q))
    (fun Q => Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q))
    (physicalNodeShift M θB hB N L u k hk C)
    (η := η) (δ := ((L+1:ℕ):ℝ)⁻¹) (K := nodeChargeConstant k hk C η)
    (P := (nodeHistoryBudget k hk C:ℝ)) (k := (k:ℝ))
    (B := physicalChildrenAverage M θB hB N L u k C η)
    (B' := Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)))
    (by positivity) (nodeChargeConstant_nonneg k hk C hη) (by positivity) (by positivity)
    hpoint (hc false) (hc true) hs
  convert hb using 1
  dsimp only [physicalShapeAverage]
  congr 3


/-- Uniform averaged producer. All old/target experiments are chosen before N
and u. The two old/delayed child contributions are controlled using full-cube
fibers, never by restricting independently averaged copies to a diagonal. -/
theorem regular_node_average (M : Model p) (θB hB : ℝ) (L : ℕ)
    (k : ℕ+) (hk : 2≤(k:ℕ)) (C : Fin k → ReducedTopology)
    {η : ℝ} (hη : 0<η) (hlarge : 4<η*(L+1:ℕ)) :
    let α := Option (ReducedTopology.node k hk C).Vertex
    let t := 2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1
    ∃ (S T : (α → Fin (L+1)) → PrescribedTree (L+1))
      (a : (Q : α → Fin (L+1)) → (S Q).Leaf)
      (q : (Q : α → Fin (L+1)) → Option (Fin t) → (T Q).Leaf)
      (J : (α → Fin (L+1)) → ℝ), ∀ (N : ℕ) (u : Spec L × ℕ → ℝ),
    η*physicalShapeAverage M θB hB N L u (.node k hk C) η ≤
      4*((L+1:ℕ):ℝ)⁻¹ +
      2*DepthAverage.average (regularShapeDomain (.node k hk C) (L+1) η) (fun Q =>
        |physicalTreeMatrixCovariance (gridExponents L) (S Q) (a Q) M θB hB N u (T Q) (q Q)|/|J Q|) +
      (4*nodeChargeConstant k hk C η+4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
        physicalChildrenAverage M θB hB N L u k C η +
      2*nodeChargeConstant k hk C η*Real.sqrt (nodeShiftBudget k C/(L+1:ℕ)) := by
  classical
  dsimp only
  let D := regularShapeDomain (.node k hk C) (L+1) η
  have hpoint (Q : Option (ReducedTopology.node k hk C).Vertex → Fin (L+1)) :
      ∃ (S T : PrescribedTree (L+1)) (a : S.Leaf)
        (q : Option (Fin (2*Fintype.card (ReducedTopology.node k hk C).Leaf-2+1)) → T.Leaf)
        (J : ℝ), ∀ N u, D Q →
      η*physicalScheduledEnergy M θB hB N L u (.node k hk C) Q ≤
        4*((L+1:ℕ):ℝ)⁻¹ +
        2*(|physicalTreeMatrixCovariance (gridExponents L) S a M θB hB N u T q|/|J|) +
        4*nodeChargeConstant k hk C η*Real.sqrt (physicalChildMass M θB hB N L u k hk C true Q) +
        2*nodeChargeConstant k hk C η*physicalNodeShift M θB hB N L u k hk C Q +
        (4*(nodeHistoryBudget k hk C:ℝ)+16*(k:ℝ))*
          Real.sqrt (physicalChildMass M θB hB N L u k hk C false Q) := by
    by_cases hQ : D Q
    · obtain ⟨S,T,a,q,J,h⟩ := regular_node_pointwise M θB hB L k hk C hη (by linarith) Q hQ
      exact ⟨S,T,a,q,J,fun N u _ => h N u⟩
    · exact ⟨single (L+1),single (L+1),singleLeaf (L+1),fun _ => singleLeaf (L+1),1,
        fun _ _ h => (hQ h).elim⟩
  choose S T a q J hpoint using hpoint
  refine ⟨S,T,a,q,J,?_⟩
  intro N u
  exact regular_node_average_inequality M θB hB N L u k hk C hη hlarge S T a q J
    (hpoint · N u)

end DilutedSpinGlass.UniversalDictionary

end

end OAI
