import Mathlib
import OAI.Probability.CriticalPercolation.GraphTopology.OrbitalNeighborhoods

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitPower_propagate_subgroup_orbit (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o)
    {u v : MulAction.orbit G.Aut o} (huv : (G.orbitPower o L).Adj u v)
    (hu : u.val∈MulAction.orbit Λ o) : v.val∈MulAction.orbit Λ o := by
  obtain ⟨φ,hφ⟩ := hu
  change φ.val • o=u.val at hφ
  have hv : v.val∈G.orbitBall (φ.val • o) L := by
    refine ⟨?_,?_⟩
    · simpa only [MulAction.orbit_smul] using v.property
    · rw [hφ]
      exact huv.2
  have hback : φ.val⁻¹ • v.val∈G.orbitBall o L := by
    have hh := (Aut.orbitBall_mem G φ.val o (φ.val⁻¹ • v.val) L)
    rw [smul_inv_smul] at hh
    exact hh.mp hv
  obtain ⟨ψ,hψ⟩ := hgen _ hback
  refine ⟨φ*ψ,?_⟩
  change (φ*ψ) • o=v.val
  change ψ • o=φ.val⁻¹ • v.val at hψ
  rw [mul_smul,hψ]
  change φ.val • (φ.val⁻¹ • v.val)=v.val
  exact smul_inv_smul _ _

lemma orbitPower_subgroup_transitive (o : V) (L : ℕ) (Λ : Subgroup G.Aut)
    (hc : (G.orbitPower o L).Connected)
    (hgen : ∀ v∈G.orbitBall o L, v∈MulAction.orbit Λ o) :
    MulAction.orbit Λ o=MulAction.orbit G.Aut o := by
  apply Set.Subset.antisymm
  · rintro v ⟨φ,hφ⟩
    exact ⟨φ.val,hφ⟩
  · intro v hv
    let o' : MulAction.orbit G.Aut o := ⟨o,MulAction.mem_orbit_self o⟩
    let v' : MulAction.orbit G.Aut o := ⟨v,hv⟩
    obtain ⟨p⟩ := hc o' v'
    have hwalk : ∀ {u w : MulAction.orbit G.Aut o} (p : (G.orbitPower o L).Walk u w),
        u.val∈MulAction.orbit Λ o → w.val∈MulAction.orbit Λ o := by
      intro u w p
      induction p with
      | nil => exact id
      | cons huw p ih =>
        exact fun hu => ih (G.orbitPower_propagate_subgroup_orbit o L Λ hgen huw hu)
    exact hwalk p (MulAction.mem_orbit_self o)

lemma dense_orbit_subgroup_representatives (o : V)
    (C : ℕ) (hdense : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C)
    (Λ : Subgroup G.Aut) (horbit : MulAction.orbit Λ o=MulAction.orbit G.Aut o) :
    ∀ v, ∃ s∈G.vertexBall o C, v∈MulAction.orbit Λ s := by
  intro v
  obtain ⟨u,hu⟩ := hdense v
  have hu' : u.val∈MulAction.orbit Λ o := by rw [horbit]; exact u.property
  obtain ⟨φ,hφ⟩ := hu'
  change φ.val • o=u.val at hφ
  refine ⟨φ.val⁻¹ • v,?_,φ,?_⟩
  · apply (Aut.vertexBall_mem G φ.val o (φ.val⁻¹ • v) C).mp
    change φ.val • (φ.val⁻¹ • v)∈G.vertexBall (φ.val • o) C
    rw [smul_inv_smul,hφ]
    exact G.vertexBall_comm.mp hu
  · change φ.val • (φ.val⁻¹ • v)=v
    exact smul_inv_smul _ _

theorem finitelyGenerated_quasiTransitive_subgroup (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) :
    ∃ Λ : Subgroup G.Aut, Group.FG Λ ∧
      MulAction.orbit Λ o=MulAction.orbit G.Aut o ∧
      ∃ S : Set V, S.Finite ∧ ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s := by
  obtain ⟨C,hC,hdense⟩ := G.orbitPower_connected hc hq o
  let B := G.orbitBall o (2*C+1)
  have hB : B.Finite := G.orbitBall_finite hl o _
  let _ := hB.fintype
  have hφ : ∀ v : B, ∃ φ : G.Aut, φ • o=v.val := fun v => v.property.1
  choose φ hφ using hφ
  let F := Finset.univ.image φ
  let Λ := Subgroup.closure (F : Set G.Aut)
  have hgen : ∀ v∈G.orbitBall o (2*C+1), v∈MulAction.orbit Λ o := by
    intro v hv
    have hf : φ ⟨v,hv⟩∈Λ := Subgroup.subset_closure
      (Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩)
    exact ⟨⟨φ ⟨v,hv⟩,hf⟩,hφ ⟨v,hv⟩⟩
  have horbit := G.orbitPower_subgroup_transitive o (2*C+1) Λ hC hgen
  refine ⟨Λ,inferInstance,horbit,G.vertexBall o C,G.vertexBall_finite hl o C,?_⟩
  exact G.dense_orbit_subgroup_representatives o C hdense Λ horbit

end CriticalPercolation.BondGraph
end
end

end OAI
