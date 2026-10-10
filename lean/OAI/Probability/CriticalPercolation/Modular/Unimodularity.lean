import Mathlib
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

structure UnimodularRoot where
  roots : Finset V
  weight : V → ℝ
  positive : ∀ u ∈ roots, 0 < weight u
  normalized : ∑ u ∈ roots, weight u = 1
  cover : ∀ v : V, ∃ u ∈ roots, ∃ φ : G.Aut, φ.vertex u = v
  balance : ∀ F : V → V → ℝ,
    (∀ (φ : G.Aut) u v, F (φ.vertex u) (φ.vertex v) = F u v) →
    (∀ u, (Function.support (F u)).Finite) →
    (∀ v, (Function.support (fun u => F u v)).Finite) →
    (∑ u ∈ roots, weight u * ∑' v, F u v) =
      ∑ v ∈ roots, weight v * ∑' u, F u v

lemma UnimodularRoot.quasiTransitive (R : G.UnimodularRoot) : G.QuasiTransitive :=
  ⟨R.roots,R.roots.finite_toSet,R.cover⟩

def bondShare (e : E) : ℝ := 1 / (G.ends e).toFinset.card

lemma bondShare_pos (e : E) : 0 < G.bondShare e := by
  apply one_div_pos.mpr
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty _)))

lemma bondShare_count (e : E) : ((G.ends e).toFinset.card : ℝ) * G.bondShare e = 1 := by
  unfold bondShare
  exact mul_one_div_cancel (ne_of_gt (by
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty _)))))

lemma Aut.bondShare (φ : G.Aut) (e : E) : G.bondShare (φ.edge e) = G.bondShare e := by
  have hfin : (G.ends (φ.edge e)).toFinset = (G.ends e).toFinset.map φ.vertex.toEmbedding := by
    ext v
    simp only [Sym2.mem_toFinset,Finset.mem_map,Equiv.toEmbedding_apply,φ.preserves,Sym2.mem_map]
  simp only [CriticalPercolation.BondGraph.bondShare,hfin,Finset.card_map]

lemma Aut.incident_iff (φ : G.Aut) (u : V) (e : E) :
    φ.vertex u ∈ G.ends (φ.edge e) ↔ u ∈ G.ends e := by
  rw [φ.preserves,Sym2.mem_map]
  simp only [φ.vertex.injective.eq_iff,exists_eq_right]

def splitBondTransport (F : V → E → ℝ) (u v : V) : ℝ :=
  ∑' e, if v ∈ G.ends e then G.bondShare e * F u e else 0

lemma splitBondTransport_zero (F : V → E → ℝ) {u v : V}
    (hv : v ∉ ⋃ e ∈ Function.support (F u), {v | v ∈ G.ends e}) :
    G.splitBondTransport F u v = 0 := by
  unfold splitBondTransport
  have hz (e : E) : (if v ∈ G.ends e then G.bondShare e * F u e else 0) = 0 := by
    by_cases he : v ∈ G.ends e
    · have hf : F u e = 0 := by
        by_contra hn
        exact hv (Set.mem_iUnion₂.mpr ⟨e,hn,he⟩)
      simp [he,hf]
    · simp [he]
  simp only [hz,tsum_zero]

lemma splitBondTransport_row_finite (F : V → E → ℝ)
    (hf : ∀ u, (Function.support (F u)).Finite) (u : V) :
    (Function.support (G.splitBondTransport F u)).Finite := by
  have endpoints_finite (edge : E) : {vertex | vertex ∈ G.ends edge}.Finite := by
    convert (G.ends edge).toFinset.finite_toSet using 1
    ext vertex
    exact Sym2.mem_toFinset.symm
  apply ((hf u).biUnion fun edge _ => endpoints_finite edge).subset
  intro v hv
  by_contra hn
  exact hv (G.splitBondTransport_zero F hn)

lemma splitBondTransport_column_finite (hl : G.LocallyFinite) (F : V → E → ℝ)
    (hf : ∀ e, (Function.support (fun u => F u e)).Finite) (v : V) :
    (Function.support (fun u => G.splitBondTransport F u v)).Finite := by
  apply ((hl v).biUnion (fun e _ => hf e)).subset
  intro u hu
  by_contra hn
  have hz (e : E) : (if v ∈ G.ends e then G.bondShare e * F u e else 0) = 0 := by
    by_cases he : v ∈ G.ends e
    · have hf : F u e = 0 := by
        by_contra hne
        exact hn (Set.mem_iUnion₂.mpr ⟨e,he,hne⟩)
      simp [he,hf]
    · simp [he]
  exact hu (by simp only [splitBondTransport,hz,tsum_zero])

lemma splitBondTransport_aut (F : V → E → ℝ)
    (hF : ∀ (φ : G.Aut) u e, F (φ.vertex u) (φ.edge e) = F u e)
    (φ : G.Aut) (u v : V) :
    G.splitBondTransport F (φ.vertex u) (φ.vertex v) = G.splitBondTransport F u v := by
  unfold splitBondTransport
  rw [← φ.edge.tsum_eq]
  simp only [Aut.incident_iff,Aut.bondShare,hF]

lemma tsum_incident_share (e : E) (a : ℝ) :
    (∑' v : V, if v ∈ G.ends e then G.bondShare e * a else 0) = a := by
  rw [tsum_eq_sum (s := (G.ends e).toFinset) (fun v hv => ite_eq_right (fun h => hv (Sym2.mem_toFinset.mpr h)))]
  calc
    _ = ∑ _v ∈ (G.ends e).toFinset, G.bondShare e * a := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left (Sym2.mem_toFinset.mp hv)]
    _ = a := by
      rw [Finset.sum_const,nsmul_eq_mul,← mul_assoc,bondShare_count,one_mul]

lemma splitBondTransport_sum_out (F : V → E → ℝ)
    (hf : ∀ u, (Function.support (F u)).Finite) (u : V) :
    (∑' v, G.splitBondTransport F u v) = ∑' e, F u e := by
  have ht (v : V) : G.splitBondTransport F u v =
      ∑ e ∈ (hf u).toFinset, if v ∈ G.ends e then G.bondShare e * F u e else 0 := by
    apply tsum_eq_sum
    intro e he
    have hz : F u e = 0 := not_not.mp (fun h => he ((hf u).mem_toFinset.mpr h))
    simp [hz]
  have hs (e : E) : Summable (fun v => if v ∈ G.ends e then G.bondShare e * F u e else 0) := by
    apply summable_of_ne_finset_zero (s := (G.ends e).toFinset)
    exact fun v hv => ite_eq_right (fun h => hv (Sym2.mem_toFinset.mpr h))
  simp only [ht]
  rw [Summable.tsum_finsetSum (fun e _ => hs e)]
  simp only [tsum_incident_share]
  exact (tsum_eq_sum (s := (hf u).toFinset) (fun e he =>
    not_not.mp (fun h => he ((hf u).mem_toFinset.mpr h)))).symm

lemma splitBondTransport_sum_in (hl : G.LocallyFinite) (F : V → E → ℝ)
    (hf : ∀ e, (Function.support (fun u => F u e)).Finite) (v : V) :
    (∑' u, G.splitBondTransport F u v) =
      ∑' e, if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0 := by
  have ht (u : V) : G.splitBondTransport F u v =
      ∑ e ∈ (hl v).toFinset, G.bondShare e * F u e := by
    unfold splitBondTransport
    rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * F u e else 0)
      (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
    apply Finset.sum_congr rfl
    intro e he
    rw [ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)]
  have hs (e : E) : Summable (fun u => G.bondShare e * F u e) :=
    (summable_of_hasFiniteSupport (hf e)).mul_left _
  simp only [ht]
  rw [Summable.tsum_finsetSum (fun e _ => hs e)]
  simp only [tsum_mul_left]
  rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0)
    (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
  apply Finset.sum_congr rfl
  intro e he
  rw [ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)]

lemma UnimodularRoot.bond_balance (R : G.UnimodularRoot) (hl : G.LocallyFinite)
    (F : V → E → ℝ) (hF : ∀ (φ : G.Aut) u e, F (φ.vertex u) (φ.edge e) = F u e)
    (hr : ∀ u, (Function.support (F u)).Finite)
    (hc : ∀ e, (Function.support (fun u => F u e)).Finite) :
    (∑ u ∈ R.roots, R.weight u * ∑' e, F u e) =
      ∑ v ∈ R.roots, R.weight v *
        ∑' e, if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0 := by
  have h := R.balance (G.splitBondTransport F) (G.splitBondTransport_aut F hF)
    (G.splitBondTransport_row_finite F hr) (G.splitBondTransport_column_finite hl F hc)
  simpa only [G.splitBondTransport_sum_out F hr,G.splitBondTransport_sum_in hl F hc] using h

end CriticalPercolation.BondGraph
end
end

end OAI
