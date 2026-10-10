import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonPlanarNeighborhood

theorem punctured_ball_connected (x : ℂ) {r : ℝ} (hr : 0<r) :
    IsConnected (ball x r\{x}) := by
  let e := OpenPartialHomeomorph.univBall x r
  have hc : IsConnected ({(0:ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 0
  have he : e '' ({(0:ℂ)}ᶜ : Set ℂ)=ball x r\{x} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzS : z∈e.source := by simp [e]
      refine ⟨?_,?_⟩
      · simpa [e,OpenPartialHomeomorph.univBall_target x hr] using e.map_source hzS
      · intro hy
        have hz0 : z=0 := by
          calc
            z=e.symm (e z) := (e.left_inv hzS).symm
            _=0 := by simpa [e] using congrArg e.symm (mem_singleton_iff.mp hy)
        exact hz (mem_singleton_iff.mpr hz0)
    · rintro ⟨hy,hyx⟩
      have hyT : y∈e.target := by simpa [e,OpenPartialHomeomorph.univBall_target x hr] using hy
      refine ⟨e.symm y,?_,e.right_inv hyT⟩
      intro hz
      have hz0 : e.symm y=0 := mem_singleton_iff.mp hz
      apply hyx
      apply mem_singleton_iff.mpr
      calc
        y=e (e.symm y) := (e.right_inv hyT).symm
        _=x := by rw [hz0]; simp [e]
  rw [←he]
  exact hc.image e (OpenPartialHomeomorph.continuous_univBall x r).continuousOn

theorem isolated_frontier_forces_punctured_ball {R : Set ℂ} (hR : IsOpen R)
    {x : ℂ} {r : ℝ} (hr : 0<r) (hx : x∈closure R) (hxR : x∉R)
    (hbound : closure R∩(ball x r\{x})⊆R) : ball x r\{x}⊆R := by
  let U := ball x r\{x}
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp
    (punctured_ball_connected x hr).isPreconnected
  let S : Set U := Subtype.val ⁻¹' R
  have hS : IsClopen S := by
    constructor
    · have he : S=Subtype.val ⁻¹' closure R := by
        ext z
        exact ⟨fun hz => subset_closure hz,fun hz => hbound ⟨hz,z.property⟩⟩
      rw [he]
      exact isClosed_closure.preimage continuous_subtype_val
    · exact hR.preimage continuous_subtype_val
  obtain ⟨y,hyB,hyR⟩ := (mem_closure_iff_nhds.mp hx) _ (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hyx : y≠x := fun h => hxR (h ▸ hyR)
  have hn : S.Nonempty := ⟨⟨y,hyB,hyx⟩,hyR⟩
  have he := hS.eq_univ hn
  intro z hz
  exact (show (⟨z,hz⟩ : U)∈S from he.symm ▸ mem_univ _)
end CannonPlanarNeighborhood

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
