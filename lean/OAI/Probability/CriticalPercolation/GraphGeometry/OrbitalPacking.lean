import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphTopology.OrbitalNeighborhoods

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitBall_packing (hl : G.LocallyFinite) (o : V) (r K : ℕ)
    (hd : (G.orbitBall o (5*r)).ncard≤K*(G.orbitBall o r).ncard) :
    ∃ F : Finset V, (↑F : Set V)⊆G.orbitBall o (4*r) ∧ F.card≤K ∧
      ∀ u∈G.orbitBall o (4*r), ∃ v∈F, u∈G.vertexBall v (2*r) := by
  let A := (G.orbitBall_finite hl o (4*r)).toFinset
  let C : Finset (Finset V) := A.powerset.filter
    (fun F => (F : Set V).PairwiseDisjoint (fun v => G.orbitBall v r))
  obtain ⟨F,hFmax⟩ := C.exists_maximal <| Finset.filter_nonempty_iff.mpr
    ⟨∅,Finset.empty_mem_powerset _,by simp⟩
  simp only [C,Finset.mem_filter,Finset.mem_powerset] at hFmax
  obtain ⟨hFA,hF⟩ := hFmax.1
  have hFo : (F : Set V)⊆G.orbitBall o (4*r) := by
    intro u hu
    exact (G.orbitBall_finite hl o (4*r)).mem_toFinset.mp (hFA hu)
  have hsub : (⋃ u∈(F : Set V), G.orbitBall u r) ⊆ G.orbitBall o (5*r) := by
    intro v hv
    obtain ⟨u,hu,hv⟩ := Set.mem_iUnion₂.mp hv
    simpa only [show 4*r+r=5*r by omega] using G.orbitBall_add (hFo hu) r hv
  have hcount : F.card*(G.orbitBall o r).ncard≤(G.orbitBall o (5*r)).ncard := by
    calc
      F.card*(G.orbitBall o r).ncard = ∑ u∈F, (G.orbitBall u r).ncard := by
        symm
        apply Finset.sum_const_nat
        intro u hu
        exact G.orbitBall_ncard_of_mem_orbit (hFo hu).1 r
      _ = (⋃ u∈(F : Set V), G.orbitBall u r).ncard := by
        rw [(F.finite_toSet).ncard_biUnion (fun u _ => G.orbitBall_finite hl u r) hF,
          finsum_mem_coe_finset]
      _ ≤ (G.orbitBall o (5*r)).ncard := Set.ncard_le_ncard hsub (G.orbitBall_finite hl o _)
  refine ⟨F,hFo,le_of_mul_le_mul_right (hcount.trans hd) (G.orbitBall_ncard_pos hl o r),?_⟩
  intro u hu
  by_cases huF : u∈F
  · exact ⟨u,huF,G.mem_vertexBall_self u _⟩
  by_cases! H : ∀ v∈F, Disjoint (G.orbitBall u r) (G.orbitBall v r)
  · refine False.elim (hFmax.not_gt ?_ (Finset.ssubset_insert huF))
    rw [Finset.insert_subset_iff,Finset.coe_insert]
    exact ⟨⟨(G.orbitBall_finite hl o (4*r)).mem_toFinset.mpr hu,hFA⟩,
      hF.insert (fun v hv _ => H v hv)⟩
  · simp_rw [Set.not_disjoint_iff] at H
    obtain ⟨v,hv,w,hwu,hwv⟩ := H
    refine ⟨v,hv,?_⟩
    simpa only [show r+r=2*r by omega] using
      G.vertexBall_add hwv.2 r (G.vertexBall_comm.mp hwu.2)

lemma displacementBall_cover_of_doubling (hl : G.LocallyFinite) (o : V) (r K : ℕ)
    (hd : (G.orbitBall o (5*r)).ncard≤K*(G.orbitBall o r).ncard) :
    CovBySMul G.Aut (K : ℝ) (G.displacementBall o (4*r)) (G.displacementBall o (2*r)) := by
  obtain ⟨F,hFo,hFK,hcover⟩ := G.orbitBall_packing hl o r K hd
  have hex : ∀ v : F, ∃ φ : G.Aut, φ • o=v.val := by
    intro v
    exact (hFo v.property).1
  choose φ hφ using hex
  let H := Finset.univ.image φ
  have hH : H.card≤K := (Finset.card_image_le).trans (by simpa using hFK)
  refine ⟨H,by exact_mod_cast hH,?_⟩
  intro ψ hψ
  have hu : ψ • o∈G.orbitBall o (4*r) := ⟨MulAction.mem_orbit _ _,hψ⟩
  obtain ⟨v,hv,huv⟩ := hcover (ψ • o) hu
  let c := φ ⟨v,hv⟩
  have hc : c∈H := Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hco : c • o=v := hφ ⟨v,hv⟩
  have hrem : c⁻¹*ψ∈G.displacementBall o (2*r) := by
    apply (Aut.vertexBall_mem G c o ((c⁻¹*ψ) • o) (2*r)).mp
    change c • ((c⁻¹*ψ) • o)∈G.vertexBall (c • o) (2*r)
    rw [←mul_smul,mul_inv_cancel_left,hco]
    exact huv
  change ψ∈(H : Set G.Aut)*G.displacementBall o (2*r)
  exact Set.mem_mul.mpr ⟨c,hc,c⁻¹*ψ,hrem,by simp⟩

lemma displacementBall_approximate_of_doubling (hl : G.LocallyFinite) (o : V) (r K : ℕ)
    (hd : (G.orbitBall o (5*r)).ncard≤K*(G.orbitBall o r).ncard) :
    IsApproximateSubgroup (K : ℝ) (G.displacementBall o (2*r)) where
  one_mem := G.one_mem_displacementBall o _
  inv_eq_self := by
    ext φ
    change φ⁻¹∈G.displacementBall o (2*r) ↔ φ∈G.displacementBall o (2*r)
    exact G.inv_mem_displacementBall
  sq_covBySMul := by
    apply (G.displacementBall_cover_of_doubling hl o r K hd).subset_left
    rw [pow_two]
    simpa only [show 2*r+2*r=4*r by omega] using G.displacementBall_mul_subset o (2*r) (2*r)

theorem displacementBall_approximate_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∀ R : ℕ, ∃ n≥R, IsApproximateSubgroup (5^(d+2) : ℝ) (G.displacementBall o (2*n)) := by
  intro R
  obtain ⟨n,hn,hd⟩ := G.orbitBall_doubling_scales hc hl hq o d hpoly R
  refine ⟨n,hn,?_⟩
  exact_mod_cast G.displacementBall_approximate_of_doubling hl o n (5^(d+2)) hd

end CriticalPercolation.BondGraph
end
end

end OAI
