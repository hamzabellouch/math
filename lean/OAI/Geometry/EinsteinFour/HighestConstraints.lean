import OAI.Geometry.EinsteinFour.HighestLinear

namespace OAI

/-! Extraction of the exact scalar equations from an actual Hessian. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem coordinate_constraint_0 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 0 + c 20 + c 35 + c 45 = 0 := by
  have h := congrArg (fun M : Mat => M 0 0) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 0 + (c 20 + (c 35 + c 45)) = 0 at h
  linear_combination h

theorem coordinate_constraint_1 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 1 + c 21 + c 36 + c 46 = 0 := by
  have h := congrArg (fun M : Mat => M 1 1) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 1 + (c 21 + (c 36 + c 46)) = 0 at h
  linear_combination h

theorem coordinate_constraint_2 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 + c 22 + c 37 + c 47 = 0 := by
  have h := congrArg (fun M : Mat => M 0 1) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 2 + (c 22 + (c 37 + c 47)) = 0 at h
  linear_combination h

theorem coordinate_constraint_3 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 3 + c 23 + c 38 + c 48 = 0 := by
  have h := congrArg (fun M : Mat => M 0 2) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 3 + (c 23 + (c 38 + c 48)) = 0 at h
  linear_combination h

theorem coordinate_constraint_4 (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (_hb : ∀ i r, divergence (raw c) i r = 0) :
    c 4 + c 24 + c 39 + c 49 = 0 := by
  have h := congrArg (fun M : Mat => M 1 2) ht
  simp [hessianTrace, ofCoordinates, Fin.sum_univ_succ] at h
  change c 4 + (c 24 + (c 39 + c 49)) = 0 at h
  linear_combination h

theorem coordinate_constraint_5 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 5 - c 12 - c 18 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_6 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 0 - c 13 + c 17 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_7 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 + c 8 - c 15 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_8 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 3 - c 7 + c 10 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 0 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_9 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 7 - c 11 - c 19 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_10 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 2 - c 14 + c 16 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_11 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 1 + c 9 - c 17 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_12 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 4 - c 6 + c 12 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 0 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_17 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 20 - c 27 - c 33 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_18 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 5 - c 28 + c 32 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_19 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 7 + c 23 - c 30 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_20 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 8 - c 22 + c 25 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 1 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_21 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 22 - c 26 - c 34 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_22 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 7 - c 29 + c 31 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_23 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 6 + c 24 - c 32 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_24 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 9 - c 21 + c 27 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 1 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_29 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 25 - c 37 - c 43 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_30 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 10 - c 38 + c 42 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_31 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 12 + c 28 - c 40 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_32 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 13 - c 27 + c 35 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 2 0)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_33 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    -c 27 - c 36 - c 44 = 0 := by
  have h := congrArg (fun q : Vec => q 0) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_34 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 12 - c 39 + c 41 = 0 := by
  have h := congrArg (fun q : Vec => q 1) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_35 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 11 + c 29 - c 42 = 0 := by
  have h := congrArg (fun q : Vec => q 2) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

theorem coordinate_constraint_36 (c : Fin 50 → ℝ)
    (_ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) :
    c 14 - c 26 + c 37 = 0 := by
  have h := congrArg (fun q : Vec => q 3) (hb 2 1)
  simp [divergence, ofCoordinates, quaternion, Fin.sum_univ_succ] at h
  linear_combination h

/-- The geometric tensor constraints imply the displayed independent system. -/
theorem equations_of_constraints (c : Fin 50 → ℝ)
    (ht : hessianTrace (raw c) = 0)
    (hb : ∀ i r, divergence (raw c) i r = 0) : Equations c where
  eq0 := coordinate_constraint_0 c ht hb
  eq1 := coordinate_constraint_1 c ht hb
  eq2 := coordinate_constraint_2 c ht hb
  eq3 := coordinate_constraint_3 c ht hb
  eq4 := coordinate_constraint_4 c ht hb
  eq5 := coordinate_constraint_5 c ht hb
  eq6 := coordinate_constraint_6 c ht hb
  eq7 := coordinate_constraint_7 c ht hb
  eq8 := coordinate_constraint_8 c ht hb
  eq9 := coordinate_constraint_9 c ht hb
  eq10 := coordinate_constraint_10 c ht hb
  eq11 := coordinate_constraint_11 c ht hb
  eq12 := coordinate_constraint_12 c ht hb
  eq17 := coordinate_constraint_17 c ht hb
  eq18 := coordinate_constraint_18 c ht hb
  eq19 := coordinate_constraint_19 c ht hb
  eq20 := coordinate_constraint_20 c ht hb
  eq21 := coordinate_constraint_21 c ht hb
  eq22 := coordinate_constraint_22 c ht hb
  eq23 := coordinate_constraint_23 c ht hb
  eq24 := coordinate_constraint_24 c ht hb
  eq29 := coordinate_constraint_29 c ht hb
  eq30 := coordinate_constraint_30 c ht hb
  eq31 := coordinate_constraint_31 c ht hb
  eq32 := coordinate_constraint_32 c ht hb
  eq33 := coordinate_constraint_33 c ht hb
  eq34 := coordinate_constraint_34 c ht hb
  eq35 := coordinate_constraint_35 c ht hb
  eq36 := coordinate_constraint_36 c ht hb

end
end PositiveEinsteinFour.HighestHessian

end OAI
