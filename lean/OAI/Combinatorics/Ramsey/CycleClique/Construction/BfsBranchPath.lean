import OAI.Combinatorics.Ramsey.CycleClique.Construction.BfsBranches
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CycleTwoPaths

namespace OAI

/-! The path up two distinct predecessor branches has no vertices in its endpoint layer internally. -/

namespace CycleClique.Construction
noncomputable def bfsBranchPath {V : Type*} (G : SimpleGraph V) (root u v : V) (p : ℕ)
    (i : Fin (2 * p + 1)) : V :=
  if i.val ≤ p then (bfsParent G root)^[i.val] u
  else (bfsParent G root)^[2 * p - i.val] v

@[simp] theorem bfsBranchPath_start {V : Type*} (G : SimpleGraph V) (root u v : V) (p : ℕ) :
    bfsBranchPath G root u v p 0 = u := by simp [bfsBranchPath]

@[simp] theorem bfsBranchPath_end {V : Type*} (G : SimpleGraph V) (root u v : V)
    {p : ℕ} (hp : 1 ≤ p) : bfsBranchPath G root u v p (Fin.last (2 * p)) = v := by
  simp [bfsBranchPath, show ¬ 2 * p ≤ p by omega]

theorem bfsBranchPath_isPath {V : Type*} {G : SimpleGraph V} {root u v : V} {p d : ℕ}
    (hu : G.Reachable root u) (hv : G.Reachable root v)
    (hdu : G.dist root u = d) (hdv : G.dist root v = d) (hp : p ≤ d)
    (hcommon : (bfsParent G root)^[p] u = (bfsParent G root)^[p] v)
    (hsplit : ∀ j < p, (bfsParent G root)^[j] u ≠ (bfsParent G root)^[j] v) :
    IsIndexedPath G (bfsBranchPath G root u v p) := by
  have hlu : ∀ j ≤ p, G.dist root ((bfsParent G root)^[j] u) = d - j := by
    intro j hj
    simpa only [hdu] using (bfsAncestor_level hu j (by omega)).2
  have hlv : ∀ j ≤ p, G.dist root ((bfsParent G root)^[j] v) = d - j := by
    intro j hj
    simpa only [hdv] using (bfsAncestor_level hv j (by omega)).2
  refine ⟨?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    by_cases hip : i.val ≤ p
    · by_cases hjp : j.val ≤ p
      · simp only [bfsBranchPath, ite_eq_left hip, ite_eq_left hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlu _ hip, hlu _ hjp] at hd
        omega
      · simp only [bfsBranchPath, ite_eq_left hip, ite_eq_right hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlu _ hip, hlv _ (by omega)] at hd
        have heq : i.val = 2 * p - j.val := by omega
        rw [← heq] at hij
        exact False.elim (hsplit i.val (by omega) hij)
    · by_cases hjp : j.val ≤ p
      · simp only [bfsBranchPath, ite_eq_right hip, ite_eq_left hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlv _ (by omega), hlu _ hjp] at hd
        have heq : j.val = 2 * p - i.val := by omega
        rw [← heq] at hij
        exact False.elim (hsplit j.val (by omega) hij.symm)
      · simp only [bfsBranchPath, ite_eq_right hip, ite_eq_right hjp] at hij
        have hd := congrArg (G.dist root) hij
        rw [hlv _ (by omega), hlv _ (by omega)] at hd
        omega
  · intro i
    have hi := i.isLt
    by_cases hbefore : i.val < p
    · have h := bfsAncestor_adjacent hu (show i.val < G.dist root u by omega)
      simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ,
        ite_eq_left (show i.val ≤ p by omega), ite_eq_left (show i.val + 1 ≤ p by omega)] using h
    · by_cases heq : i.val = p
      · have h := (bfsAncestor_adjacent hv (show p - 1 < G.dist root v by omega)).symm
        have hpone : p - 1 + 1 = p := by omega
        have hnext : 2 * p - (p + 1) = p - 1 := by omega
        simp only [hpone] at h
        simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ, heq,
          ite_eq_left (show p ≤ p by omega), ite_eq_right (show ¬ p + 1 ≤ p by omega),
          hnext, hcommon] using h
      · have h := (bfsAncestor_adjacent hv
          (show 2 * p - (i.val + 1) < G.dist root v by omega)).symm
        have hprev : 2 * p - (i.val + 1) + 1 = 2 * p - i.val := by omega
        simpa only [bfsBranchPath, Fin.val_castSucc, Fin.val_succ,
          ite_eq_right (show ¬ i.val ≤ p by omega),
          ite_eq_right (show ¬ i.val + 1 ≤ p by omega), hprev] using h

theorem bfsBranchPath_internal_level {V : Type*} {G : SimpleGraph V} {root u v : V}
    {p d : ℕ} (hu : G.Reachable root u) (hv : G.Reachable root v)
    (hdu : G.dist root u = d) (hdv : G.dist root v = d) (hp : p ≤ d)
    (i : Fin (2 * p + 1)) (hi : 0 < i.val) (hilast : i.val < 2 * p) :
    G.dist root (bfsBranchPath G root u v p i) < d := by
  by_cases hip : i.val ≤ p
  · have h := (bfsAncestor_level hu i.val (by omega)).2
    simp only [bfsBranchPath, ite_eq_left hip]
    rw [h, hdu]
    omega
  · have h := (bfsAncestor_level hv (2 * p - i.val) (by omega)).2
    simp only [bfsBranchPath, ite_eq_right hip]
    rw [h, hdv]
    omega

end CycleClique.Construction

end OAI
