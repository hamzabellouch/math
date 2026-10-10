import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def pickSingleton {X : Type*} [LinearOrder X] (K : Finset X) (w : X → ℚ) : Finset X :=
  if hK : K.Nonempty then
    let m := (K.image w).min' (hK.image w)
    let A := K.filter (fun a => w a=m)
    have hA : A.Nonempty := by
      obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image w) (hK.image w))
      exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
    {A.min' hA}
  else ∅

theorem pickSingleton_spec {X : Type*} [LinearOrder X] (K : Finset X) (w : X → ℚ)
    (hK : K.Nonempty) : ∃ a ∈ K, pickSingleton K w={a} ∧ ∀ b ∈ K, w a ≤ w b := by
  let m := (K.image w).min' (hK.image w)
  let A := K.filter (fun a => w a=m)
  have hA : A.Nonempty := by
    obtain ⟨a,ha,he⟩ := mem_image.mp (min'_mem (K.image w) (hK.image w))
    exact ⟨a,mem_filter.mpr ⟨ha,he⟩⟩
  let a := A.min' hA
  have ha := mem_filter.mp (min'_mem A hA)
  refine ⟨a,ha.1,?_,?_⟩
  · simp only [pickSingleton,dite_eq_left hK,a,A,m]
  · intro b hb
    rw [show w a=m from ha.2]
    exact min'_le _ _ (mem_image_of_mem w hb)

def rationalRegion (I : Instance) (r : Fin I.n → ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  I.clients.filter (fun j => 3*I.distance j t ≤ r t)

def rationalCandidates (I : Instance) (F : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  F.filter (fun a => I.distance t a ≤ δ*r t)

def localWeight (I : Instance) (r : Fin I.n → ℚ) (B : Finset (Fin I.n))
    (t a : Fin I.n) : ℚ :=
  ∑ j ∈ rationalRegion I r t, rationalNearest I j (insert a B)

def localChoice (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  pickSingleton (rationalCandidates I F r δ t) (localWeight I r B t)

def completionSet (I : Instance) (F B G : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) : Finset (Fin I.n) :=
  B ∪ G.biUnion (localChoice I F B r δ)

end MetricKMedian.Reduction
end
end

end OAI
