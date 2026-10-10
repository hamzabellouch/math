import Mathlib
import OAI.Analysis.Commutator.FreePropagationEstimate
import OAI.Analysis.Commutator.RepresentedLocalModule

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open Filter Topology ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

variable (hB : ∀ n d (x : letterSpace t S i) v,
  G (repeatedOutput t S f hf hS hfree hij d x n v)=
    repeatedOutput t S f hf hS hfree hij d x n (B n v))

variable (hGL : ∀ d : D, G.comp (t.functional.gnsStarAlgHom (f d))=
  (t.functional.gnsStarAlgHom (f d)).comp G)

variable (M : VonNeumannAlgebra t.functional.GNS)
  (hM : ∀ a : A, t.functional.gnsStarAlgHom a∈M)

include hB hGL hM in
theorem propagation_from_corner {κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : letterSpace t S j) (hs : ‖s‖=1)
    (q : D) (hq : IsStarProjection q)
    (w : κ → D)
    (hcol : ∀ i j, star (w i)*w j=if i=j then q else 0)
    (hinit : ∀ i, q*star (w i)=star (w i))
    (htotal : ∑ i, w i*star (w i)=1)
    (c : ℝ) (hc : 0≤c)
    (x : ℕ → letterSpace t S i) (hx : ∀ n, ‖x n‖=1)
    (hxq : ∀ n, letterValue t S i (x n)*f q=letterValue t S i (x n))
    (hxx : ∀ n, star (letterValue t S i (x n))*letterValue t S i (x n)=(c:ℂ) • f q)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (letterValue t S i (x n)))‖≤1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (letterValue t S i (x n)*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (R : ℝ)
    (hR : ∀ n, ‖(letterValue t S j s*letterValue t S i (x n))^k*letterValue t S j s‖≤R)
    (ε : ℝ) (hε : 0≤ε)
    (hsmall : ∀ a : t.functional.GNS →L[ℂ] t.functional.GNS, a∈M →
      t.functional.gnsStarAlgHom (f q)*a=a → a*t.functional.gnsStarAlgHom (f q)=a →
        ‖G.comp a-a.comp G‖≤ε*‖a‖)
    (v : multiplicityLevel t S j 0) :
    ‖B (k+1) (repeatInsertion t S s hs (k+1) v)-
      repeatInsertion t S s hs (k+1) (B 0 v)‖≤32*ε*‖v‖ := by
  let L := t.functional.gnsStarAlgHom
  let ξ := L (f q) (blockEmbedding t S hfree hij 0 v)
  have hfix : L (f q) ξ=ξ := by
    change (L (f q)*L (f q)) _=L (f q) _
    rw [←map_mul,←map_mul,hq.isIdempotentElem.eq]
  have hc' (i j : κ) : star (f (w i))*f (w j)=if i=j then f q else 0 := by
    simpa only [map_mul,map_star,apply_ite,map_zero] using congrArg f (hcol i j)
  have hi' (i : κ) : f q*star (f (w i))=star (f (w i)) := by
    simpa only [map_mul,map_star] using congrArg f (hinit i)
  have ht' : ∑ i, f (w i)*star (f (w i))=1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg f htotal
  obtain ⟨T,hT,hn⟩ := MatrixCornerImplementation.exists_represented_local_module
    L M hM (hq.map f) (fun i => f (w i)) hc' hi' ht' G (hGL q)
    (fun i => hGL (w i)) ξ hfix hε hsmall
  have h := propagation_of_local_module t S f hf hS hfree hij G B hB s hs q hq c hc
    x hx hxq hxx hxs hmoment hgen k R hR (16*ε) (by positivity) v T hT hn
  convert h using 1; ring

end Kadison.FreeBlocks

end

end
end

end OAI
