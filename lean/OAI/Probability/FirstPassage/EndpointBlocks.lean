import OAI.Probability.FirstPassage.EndpointGeometry
import OAI.Probability.FirstPassage.GridConnections

namespace OAI

namespace PlanarFPP
open Set Finset

theorem gridConnections_block (w : Edge → ℝ) (b m₀ K A R H : ℝ)
    (hK : 0 ≤ K) (hH : 1 ≤ H) (k m J : ℕ) (hJ : 1 ≤ J)
    (hg : w ∈ gridConnectionsEvent b m₀ K A R k m J)
    (j : ℕ) (hj : J ≤ j ∧ j ≤ gridLastLevel m)
    (he : (K+200)*(j : ℝ)^2*(gridWidth k j) ≤ H)
    (X : ℤ) (hX : gridMesh m j ∣ X) (n : ℕ)
    (hlo : -(A+4)*(2 : ℝ)^m ≤ (X : ℝ))
    (hhi : ((X+(n : ℤ)*gridMesh m j : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m)
    (r : ℝ) (hr : |r| ≤ R*(2 : ℝ)^k) :
    ∃ ds, endpointVertex b r X+displacement ds=
        endpointVertex b r (X+(n : ℤ)*gridMesh m j) ∧
      pathCost w (endpointVertex b r X) ds ≤
        m₀*((n : ℤ)*gridMesh m j : ℤ)+(n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) ∧
      PathIn (endpointVertex b r X) ds {z | X-gridMesh m j ≤ z.1 ∧
        z.1 ≤ X+(n : ℤ)*gridMesh m j+gridMesh m j ∧ |transverse b z-r| ≤ H} := by
  let d := gridMesh m j
  let p (i : ℕ) := endpointVertex b r (X+(i : ℤ)*d)
  let S : Set Vertex := {z | X-d ≤ z.1 ∧ z.1 ≤ X+(n : ℤ)*d+d ∧ |transverse b z-r| ≤ H}
  let c : ℝ := m₀*d+(K+200)*(j : ℝ)^2*gridWidth k j
  have hd : 0 < d := gridMesh_pos m j
  have hp0 : p 0 ∈ S := by
    dsimp [p,S,endpointVertex]
    refine ⟨by omega,?_,?_⟩
    · have hn : (0 : ℤ) ≤ n := by positivity
      nlinarith
    · simpa [endpointVertex] using (endpointVertex_close b r X).le.trans hH
  have step (i : ℕ) (hi : i < n) :
      ∃ ds, p i+displacement ds=p (i+1) ∧ pathCost w (p i) ds ≤ c ∧ PathIn (p i) ds S := by
    have hdiv : d ∣ X+(i : ℤ)*d := dvd_add hX (dvd_mul_left _ _)
    obtain ⟨q,hq⟩ := hdiv
    have hq' : gridMesh m j*q=X+(i : ℤ)*d := hq.symm
    have hicol : (X : ℝ) ≤ ((X+(i : ℤ)*d : ℤ) : ℝ) := by
      exact_mod_cast (show X ≤ X+(i : ℤ)*d by have h : 0 ≤ (i : ℤ)*d := mul_nonneg (by positivity) hd.le; omega)
    have hiend : X+(i : ℤ)*d+d ≤ X+(n : ℤ)*d := by
      have hi' : (i : ℤ)+1 ≤ n := by omega
      nlinarith
    have hir : ((X+(i : ℤ)*d+d : ℤ) : ℝ) ≤ (A+4)*(2 : ℝ)^m := by
      exact (by exact_mod_cast hiend : ((X+(i : ℤ)*d+d : ℤ) : ℝ) ≤ ((X+(n : ℤ)*d : ℤ) : ℝ)).trans hhi
    obtain ⟨ds,hend,hcost,hin⟩ := gridConnectionsEvent_paths w b m₀ K A R hK k m J hJ hg j hj q
      ⟨by simpa [hq'] using hlo.trans hicol,by simpa [hq'] using hir⟩ r hr (p i) (p (i+1))
      ⟨by simpa [p,endpointVertex] using hq'.symm,(endpointVertex_close b r _).le⟩
      ⟨by simp [p,endpointVertex,hq',Nat.cast_add,Nat.cast_one]; ring,(endpointVertex_close b r _).le⟩
    refine ⟨ds,hend,hcost,?_⟩
    intro t ht
    have hz := hin t ht
    rw [hq'] at hz
    change X+(i : ℤ)*d-d ≤ (p i+displacement (ds.take t)).1 ∧
      (p i+displacement (ds.take t)).1 ≤ X+(i : ℤ)*d+2*d ∧
      |transverse b (p i+displacement (ds.take t))-r| ≤ (K+200)*(j : ℝ)^2*gridWidth k j at hz
    change X-d ≤ (p i+displacement (ds.take t)).1 ∧
      (p i+displacement (ds.take t)).1 ≤ X+(n : ℤ)*d+d ∧ _
    refine ⟨?_,?_,hz.2.2.trans he⟩
    · have hi0 : (0 : ℤ) ≤ i := by positivity
      nlinarith [hz.1]
    · nlinarith [hz.2.1]
  obtain ⟨ds,hend,hcost,hin⟩ := exists_path_chain w p S (fun _ => c) n hp0 step
  refine ⟨ds,by simpa [p] using hend,?_,by simpa [p,S] using hin⟩
  have heq : (∑ _i ∈ range n,c) =
      m₀*((n : ℤ)*gridMesh m j : ℤ)+(n : ℝ)*((K+200)*(j : ℝ)^2*gridWidth k j) := by
    simp [c,d]
    ring
  rw [heq] at hcost
  simpa [p] using hcost

end PlanarFPP

end OAI
