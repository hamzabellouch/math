import OAI.Analysis.PlanarPacking.Entire
import OAI.Analysis.PlanarPacking.KernelDerivative
import OAI.Analysis.PlanarPacking.DataSplit
import OAI.Analysis.PlanarPacking.FixedRHS

namespace OAI

/-!
# Jets of the exact cardinal interpolants

The exact interpolation equations give value and derivative contacts on the triangular shell radii.
-/

namespace SharpPlanar
noncomputable def exactData₁ : CardinalData := fixed₁ exactList₁
noncomputable def exactData₂ : CardinalData := fixed₂ exactList₂
noncomputable def H₁ (s : ℝ) : ℝ := cardinal exactData₁ s+K exactData₂ 0 s
noncomputable def H₂ (s : ℝ) : ℝ := cardinal exactData₂ s+K exactData₁ 0 s
lemma H₁_hasDerivAt (s : ℝ) :
    HasDerivAt H₁ (cardinalSeries exactData₁ 1 s+K exactData₂ 1 s) s :=
  (cardinal_hasDerivAt exactData₁ s).add (K_hasDerivAt exactData₂ 0 s)
lemma H₂_hasDerivAt (s : ℝ) :
    HasDerivAt H₂ (cardinalSeries exactData₂ 1 s+K exactData₁ 1 s) s :=
  (cardinal_hasDerivAt exactData₂ s).add (K_hasDerivAt exactData₁ 0 s)
lemma exactLists_coordinate (ni : Node×Bool) :
    exactList₁ ni=transformedJets exactData₂ ni-contactList ni ∧
    exactList₂ ni=transformedJets exactData₁ ni := by
  have h1 := congrArg (fun x : X => x ni) exactLists_equations.1
  have h2 := congrArg (fun x : X => x ni) exactLists_equations.2
  simp only [g₁,g₂,lp.coeFn_sub,Pi.sub_apply] at h1 h2
  change exactList₁ ni-S exactList₂ ni=transformedJets (fixed₂ 0) ni-contactList ni at h1
  change exactList₂ ni-S exactList₁ ni=transformedJets (fixed₁ 0) ni at h2
  simp only [exactData₁,exactData₂]
  rw [transformedJets_fixed₁ exactList₁ ni,transformedJets_fixed₂ exactList₂ ni]
  constructor <;> linarith
lemma contactList_apply (n : Node) (d : Bool) :
    contactList (n,d)=if n.val=1 ∧ d=true then 1 else 0 := by
  classical
  unfold contactList columnVector
  rw [lp.single_apply]
  by_cases hn : n.val=1
  · have he : n=firstNode := Subtype.ext hn
    subst n
    cases d <;> simp [firstNode]
  · have he : n≠firstNode := by intro hh; exact hn (congrArg Subtype.val hh)
    simp [hn,he]
lemma H₁_jets (n : Node) : H₁ n.val=0 ∧ deriv H₁ n.val=if n.val=1 then -Q n.val else 0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).1
  have hd := (exactLists_coordinate (n,true)).1
  simp only [transformedJets,Bool.false_eq_true,ite_false,ite_true,contactList_apply,
    and_false,and_true] at hc hd
  have hv := (cardinal_jets exactData₁ n).1
  have hj := (cardinal_jets exactData₁ n).2
  change cardinal exactData₁ n.val=Q n.val*exactList₁ (n,false) at hv
  change deriv (cardinal exactData₁) n.val=
    Q n.val*(exactList₁ (n,true)+D n.val*exactList₁ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₁ _).deriv] at hj
  constructor
  · unfold H₁; rw [hv,hc]; field_simp; ring
  · rw [(H₁_hasDerivAt _).deriv,hj,hc,hd]
    split <;> field_simp <;> ring
lemma H₂_jets (n : Node) : H₂ n.val=0 ∧ deriv H₂ n.val=0 := by
  have hq := (Q_pos n.val).ne'
  have hc := (exactLists_coordinate (n,false)).2
  have hd := (exactLists_coordinate (n,true)).2
  simp only [transformedJets,Bool.false_eq_true,ite_false,ite_true] at hc hd
  have hv := (cardinal_jets exactData₂ n).1
  have hj := (cardinal_jets exactData₂ n).2
  change cardinal exactData₂ n.val=Q n.val*exactList₂ (n,false) at hv
  change deriv (cardinal exactData₂) n.val=
    Q n.val*(exactList₂ (n,true)+D n.val*exactList₂ (n,false)) at hj
  rw [(cardinal_hasDerivAt exactData₂ _).deriv] at hj
  constructor
  · unfold H₂; rw [hv,hc]; field_simp; ring
  · rw [(H₂_hasDerivAt _).deriv,hj,hc,hd]
    field_simp; ring
end SharpPlanar

end OAI
