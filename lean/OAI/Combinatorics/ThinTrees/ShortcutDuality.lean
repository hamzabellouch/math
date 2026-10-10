import OAI.Combinatorics.ThinTrees.Duality

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

abbrev point (v : Fin n) : Fin n → ℝ := Pi.single v 1

def incidence (e : Fin m) : Fin n → ℝ := point (G.left e) - point (G.right e)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

abbrev ProperCut (n : ℕ) := {S : Finset (Fin n) // S.Nonempty ∧ S ≠ univ}

def cutIndicator (S : Finset (Fin n)) (v : Fin n) : ℝ := if v ∈ S then 1 else 0

lemma cutIndicator_binary (S : Finset (Fin n)) (v : Fin n) :
    cutIndicator S v=0 ∨ cutIndicator S v=1 := by
  by_cases hv : v ∈ S <;> simp [cutIndicator,hv]

lemma cutIndicator_energy (S : Finset (Fin n)) :
    (∑e, (∑v, cutIndicator S v*G.incidence e v)^2)=((G.cut univ S).card : ℝ) := by
  simp only [G.eval_incidence]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
    simp [cutIndicator,hl,hr]

lemma binary_matrix_energy (X : Matrix (Fin h) (Fin n) ℝ)
    (hX : ∀i v, X i v=0 ∨ X i v=1) :
    (∑e, ∑i, (X*Matrix.of (fun v e => G.incidence e v)) i e ^2)=
      ∑e, l1dist (fun i => X i (G.left e)) (fun i => X i (G.right e)) := by
  apply sum_congr rfl
  intro e _
  unfold l1dist
  apply sum_congr rfl
  intro i _
  change (∑v, X i v*G.incidence e v)^2 = |X i (G.left e)-X i (G.right e)|
  rw [G.eval_incidence]
  rcases hX i (G.left e) with hl | hl <;> rcases hX i (G.right e) with hr | hr <;>
    simp [hl,hr]

lemma contraction_embedding (X : Matrix (Fin h) (Fin n) ℝ)
    (hX : ∀i v, X i v=0 ∨ X i v=1) (U : Matrix (Fin m) (Fin h) ℝ)
    (hU : Uᵀ*U ≤ 1) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (fun i => X i u) (fun i => X i v) := by
  dsimp
  intro u v
  have hh := Polar.norm_sq_mulVec_le hU (fun i => X i u-X i v)
  have heq : (WithLp.toLp 2 (U *ᵥ (fun i => X i u)) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (U *ᵥ (fun i => X i v)) =
      WithLp.toLp 2 (U *ᵥ (fun i => X i u-X i v)) := by
    rw [show (fun i => X i u-X i v)=(fun i => X i u)-(fun i => X i v) from rfl,mulVec_sub]
    rfl
  rw [heq,EuclideanSpace.norm_sq_eq]
  have hdist : (fun i => X i u-X i v) ⬝ᵥ (fun i => X i u-X i v)=
      l1dist (fun i => X i u) (fun i => X i v) := by
    unfold dotProduct l1dist
    apply sum_congr rfl
    intro i _
    rcases hX i u with hu | hu <;> rcases hX i v with hv | hv <;> simp [hu,hv]
  rw [←hdist]
  simpa only [dotProduct,PiLp.toLp_apply,Real.norm_eq_abs,←pow_two,sq_abs] using hh

lemma contraction_edge_diag (X : Matrix (Fin h) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin h) ℝ) (e : Fin m) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    (Y (G.left e)-Y (G.right e)).ofLp e =
      (U*(X*Matrix.of (fun v e => G.incidence e v))) e e := by
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) = _
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) =
    ∑i, U e i*(∑v, X i v*G.incidence e v)
  simp_rw [G.eval_incidence,mul_sub]
  rw [sum_sub_distrib]

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

def shortcutCoefficient (q L R : ℕ) (α ε : ℝ) : ℝ :=
  2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*((α*truncationGain α/32)^ε/(6912*(1024/ε^2)))*truncationGain α)

lemma shortcutCoefficient_nonneg (q L R : ℕ) {α ε : ℝ} (hα : 0 ≤ α) :
    0 ≤ shortcutCoefficient q L R α ε := by
  unfold shortcutCoefficient
  have hg := (truncationGain_pos α).le
  positivity

lemma binary_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R)
    (X : Matrix (Fin h) (Fin n) ℝ) (hX : ∀i v, X i v=0 ∨ X i v=1)
    (U : Matrix (Fin m) (Fin h) ℝ) (hU : Uᵀ*U ≤ 1)
    (hpositive : ∀e, 0 ≤ (U*(X*Matrix.of (fun v e => G.incidence e v))) e e) :
    (∑t : M, (∑e ∈ H.parentBoundary G t, (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2/
      ((H.parentBoundary G t).card : ℝ)) ≤
      shortcutCoefficient q L R α ε*(∑e, ∑i, (X*Matrix.of (fun v e => G.incidence e v)) i e ^2) := by
  let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
  have hh := hierarchy_numerator_bound hq hL hR hk (fun v i => hX i v) hconn M Y hM hroot
    hα hα1 he he1 hρ hρsmall (contraction_embedding X hX U hU)
    (fun e => by simpa only [Y,G.contraction_edge_diag] using hpositive e)
    hsmall hassign hratio hlogL hlogR
  rw [sum_coe_sort M (fun t => (∑e ∈ H.parentBoundary G t,
    (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2/((H.parentBoundary G t).card:ℝ)),
    G.binary_matrix_energy X hX]
  simpa only [Y,G.contraction_edge_diag,shortcutCoefficient] using hh

lemma exists_shortcut_explicit {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R)
    {η : ℝ} (hη : 0 < η) :
    ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
      (∀t ∈ M, ShortcutDual.boundaryAverage G.incidence (H.parentBoundary G) t D <
        shortcutCoefficient q L R α ε+η) ∧
      (∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
        cutIndicator S ⬝ᵥ (D *ᵥ cutIndicator S) < ((G.cut univ S).card : ℝ)) := by
  have hd (S : ProperCut n) : 0 < ((G.cut univ S).card : ℝ) :=
    Nat.cast_pos.mpr (hq.trans_le (hk S.val S.property.1 S.property.2))
  obtain ⟨D,hD,hb,hc⟩ := ShortcutDual.shortcut_of_binary_bound G.incidence
    (fun t : M => H.parentBoundary G t) (fun S : ProperCut n => cutIndicator S.val)
    (fun S : ProperCut n => ((G.cut univ S.val).card : ℝ))
    (fun S v => cutIndicator_binary S.val v) hd (fun S => G.cutIndicator_energy S.val)
    (shortcutCoefficient_nonneg q L R hα.le)
    (fun _ X hX U hU hp => binary_numerator_bound hq hL hR hk hconn M hM hroot
      hα hα1 he he1 hρ hρsmall hsmall hassign hratio hlogL hlogR X hX U hU hp) hη
  exact ⟨D,hD,fun t ht => hb ⟨t,ht⟩,fun S hS hS' => hc ⟨S,hS,hS'⟩⟩

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
