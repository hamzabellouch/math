import Mathlib
import OAI.Geometry.Cannon.PlanarGraphs.TraceCard
import OAI.Geometry.Cannon.PlaneTopology.VertexNearCard

namespace OAI

section
section
section
noncomputable section
namespace CannonCarrierCharging
open Set Metric unitInterval CannonEmbeddedArc CannonEmbeddedArc.Arc CannonIncidence

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X]

theorem uniform_original_charging_counts (Q : ℕ) (C L : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q C) (hC : 0≤C) (hL : 1≤L)
    (N : ℕ) :
    ∃ kr kc : ℕ, ∀ (r M : ℝ),0<r → 1≤M → (L+4)*r≤1 →
      ∀ T : Finset X,(∀ x∈T,∀ y∈T,x≠y → r≤dist x y) →
      (∀ x : X,∃ y∈T,dist x y≤r) →
      ∀ {ι : Type*} [Fintype ι],∀ H : ι → Arc ℂ,∀ e : ℂ → X,
      (∀ x : X,Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) →
      (∀ x : X,(T.filter (fun y=>dist x y<(L+3)*r)).card≤kr) ∧
      (∀ x : X,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*r}≤kc) := by
  classical
  obtain ⟨kr,hkr⟩:=CannonPacking.exists_overlap_bound Q C (L+3) 1 hpack hC (by linarith) zero_lt_one
  obtain ⟨B,hB⟩:=CannonIncidence.uniform_larger_trace Q C (L+3) hpack hC (by linarith)
  refine ⟨kr,2*(B*N),?_⟩
  intro r M hr hM hscale T hsep hcov ι _ H e hN
  constructor
  · intro x
    apply (Finset.card_le_card (show T.filter (fun y=>dist x y<(L+3)*r)⊆
      T.filter (fun y=>dist x y≤(L+3)*r) from fun y hy=>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2.le⟩)).trans
    apply hkr id T x r hr
    · rw [max_eq_left (by linarith : (1:ℝ)≤L+3)]
      nlinarith
    · simpa only [id_eq,one_mul] using hsep
  · intro x
    have htrace (center : X) (radius : ℝ) :
        traceCard (fun i=>range (fun t:I=>e (H i t))) (ball center radius)=
          Nat.card {i : ι | ∃ t:I,dist (e (H i t)) center<radius} := by
      have heq : {i : ι | (range (fun t:I=>e (H i t))∩ball center radius).Nonempty}=
          {i : ι | ∃ t:I,dist (e (H i t)) center<radius} := by
        ext index
        constructor
        · rintro ⟨point,⟨parameter,rfl⟩,hpoint⟩
          exact ⟨parameter,hpoint⟩
        · rintro ⟨parameter,hparameter⟩
          exact ⟨e (H index parameter),mem_range_self parameter,hparameter⟩
      simp only [traceCard,←heq,Nat.card_eq_fintype_card,Fintype.card_subtype,Set.mem_ofPred_eq]
    have hb:=hB r M hr hM (by linarith) T hsep hcov (fun i=>range (fun t:I=>e (H i t))) N
      (by
        intro center
        rw [htrace]
        exact hN center) x
    have hb' : Nat.card {i : ι | ∃ t:I,dist (e (H i t)) x<(L+3)*r}≤B*N := by
      simpa only [htrace] using hb
    exact (vertex_near_card_le H e x ((L+3)*r)).trans (Nat.mul_le_mul_left 2 hb')
end CannonCarrierCharging

end
end
end
end

end OAI
