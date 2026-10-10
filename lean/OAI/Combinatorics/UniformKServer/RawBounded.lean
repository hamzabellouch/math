import Mathlib
import OAI.Combinatorics.UniformKServer.RawRows

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawBounded
open RawArithmetic RawWords RawTable RawPath RawTyped RawExpansion RawCertificate RawRows

theorem traces_length {R : Type*} {k : ℕ} (w : List R) (h : List (R×Fin k))
    (hh : h∈PathExpansion.traces k w) : h.length=w.length := by
  induction w generalizing h with
  | nil=>simpa [PathExpansion.traces] using hh
  | cons r w ih=>
    obtain ⟨l,hl,hh⟩:=List.mem_flatten.mp hh
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hl
    obtain ⟨h',hh',rfl⟩:=List.mem_map.mp hh
    simp [ih h' hh']

theorem weight_complete {n k H b : ℕ} (hk : 0<k) (T : List ℕ)
    (p : List (Fin n)) (c : Configuration n k) (h : History n k)
    (hp : p.length+h.length≤H) :
    PathExpansion.weight (kernel T) next (p,c) h=
      PathExpansion.weight (complete hk H b T) next (p,c) h := by
  induction h generalizing p c with
  | nil=>rfl
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    have hp' : p.length≤H := by simp only [List.length_cons] at hp;omega
    simp only [PathExpansion.weight,complete,ite_eq_left hp',next]
    rw [ih]
    simp only [List.length_append,List.length_cons,List.length_nil] at *
    omega

theorem expected_eq {n k H b : ℕ} (hk : 0<k) (d : RationalMetric n) (draw : List Q)
    (hd : ∀x y : Fin n,value (dist n draw x.val y.val)=d.distance x y)
    (T : List ℕ) (hrows : rowsOK n k H b T=true)
    (p : List (Fin n)) (c : Configuration n k) (w : List (Fin n))
    (hw : p.length+w.length≤H) :
    (value (expected n k b draw T (requests p) (config c) (requests w)):ℝ)=
      BitSampling.rowCost (b:=b) (complete hk H b T) next (charge d) (p,c) w := by
  rw [expected_value]
  push_cast
  rw [total_eq d draw hd]
  have he : ((PathExpansion.traces k w).map fun h=>
      (PathExpansion.weight (kernel T) next (p,c) h:ℝ)*
        PathExpansion.movement next (charge d) (p,c) h)=
      (PathExpansion.traces k w).map (fun h=>
        (PathExpansion.weight (complete hk H b T) next (p,c) h:ℝ)*
          PathExpansion.movement next (charge d) (p,c) h) := by
    apply List.map_congr_left
    intro h hh
    rw [weight_complete hk T p c h (by simpa only [traces_length w h hh] using hw)]
  rw [he,PathExpansion.sum_weight_cost _ (RawRows.total hk hrows)]
  simp only [requests,List.length_map,pow_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

end UniformKServer.RawBounded

end


end

end OAI
