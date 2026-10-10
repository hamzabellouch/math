import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphAction
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalPower

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitPower (o : V) (L : ℕ) : SimpleGraph (MulAction.orbit G.Aut o) :=
  G.powerOn (MulAction.orbit G.Aut o) L

def orbitPowerHom (o : V) (L : ℕ) : G.Aut →*
    (G.orbitPower o L ≃g G.orbitPower o L) where
  toFun φ :=
    { toEquiv := MulAction.toPerm φ
      map_rel_iff' := by
        intro x y
        change (φ • x≠φ • y ∧ (φ • y).val∈G.vertexBall (φ • x).val L) ↔
          (x≠y ∧ y.val∈G.vertexBall x.val L)
        exact and_congr (MulAction.toPerm φ).injective.ne_iff
          (Aut.vertexBall_mem G φ x.val y.val L) }
  map_one' := by apply RelIso.ext; intro x; change (1 : G.Aut) • x=x; exact one_smul _ _
  map_mul' φ ψ := by
    apply RelIso.ext; intro x
    change (φ*ψ) • x=φ • (ψ • x)
    exact mul_smul _ _ _

lemma orbitPower_transitive (o : V) (L : ℕ)
    (u v : MulAction.orbit G.Aut o) :
    ∃ φ∈(G.orbitPowerHom o L).range, φ u=v := by
  obtain ⟨φ,hφ⟩ := MulAction.exists_smul_eq G.Aut u v
  exact ⟨G.orbitPowerHom o L φ,⟨φ,rfl⟩,hφ⟩

lemma orbitPower_connected (hc : G.fullGraph.Connected) (hq : G.QuasiTransitive)
    (o : V) : ∃ C : ℕ, (G.orbitPower o (2*C+1)).Connected ∧
      (∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C) := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  have hd : ∀ v, ∃ u : MulAction.orbit G.Aut o, u.val∈G.vertexBall v C := by
    intro v
    obtain ⟨φ,hφ⟩ := hC v
    exact ⟨⟨φ.vertex o,⟨φ,rfl⟩⟩,hφ⟩
  exact ⟨C,G.powerOn_connected hc hd,hd⟩

lemma orbitPower_ball_ncard (o : V) (L n : ℕ) (u v : MulAction.orbit G.Aut o) :
    {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n}.ncard =
    {w | ∃ p : (G.orbitPower o L).Walk v w, p.length≤n}.ncard := by
  obtain ⟨φ,hφ⟩ := MulAction.exists_smul_eq G.Aut u v
  subst v
  let f := G.orbitPowerHom o L φ
  have he : f '' {w | ∃ p : (G.orbitPower o L).Walk u w, p.length≤n} =
      {w | ∃ p : (G.orbitPower o L).Walk (φ • u) w, p.length≤n} := by
    ext w
    constructor
    · rintro ⟨z,⟨p,hp⟩,rfl⟩
      exact ⟨p.map f.toHom,(SimpleGraph.Walk.length_map f.toHom p).le.trans hp⟩
    · rintro ⟨p,hp⟩
      refine ⟨f.symm w,?_,f.apply_symm_apply w⟩
      have hp' : ∃ q : (G.orbitPower o L).Walk (f.symm (f u)) (f.symm w), q.length≤n :=
        ⟨p.map f.symm.toHom,(SimpleGraph.Walk.length_map f.symm.toHom p).le.trans hp⟩
      rw [show f.symm (f u)=u from f.symm_apply_apply u] at hp'
      exact hp'
  rw [← he,Set.ncard_image_of_injective _ f.injective]

end CriticalPercolation.BondGraph
end
end
end

end OAI
