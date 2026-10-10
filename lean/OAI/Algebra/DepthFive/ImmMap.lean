import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section
universe u v

namespace Problem335

/-- Iterated matrix multiplication commutes with change of coefficient semiring. -/
@[simp] theorem map_imm {K : Type u} {L : Type v} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (n : ℕ) : MvPolynomial.map f (imm K n) = imm L n := by
  classical
  by_cases hn : 0 < n
  · simp only [imm, dite_eq_left hn]
    let F := (MvPolynomial.map (σ := Fin n × Fin n × Fin n) f).mapMatrix (m := Fin n)
    have h := F.map_list_prod (List.ofFn (fun t : Fin n => immLayer K n t))
    have hm : (List.ofFn (fun t : Fin n => immLayer K n t)).map F =
        List.ofFn (fun t : Fin n => immLayer L n t) := by
      simp only [List.map_ofFn]
      congr 1
      funext t i j
      simp [F, immLayer]
    change F (List.ofFn (fun t : Fin n => immLayer K n t)).prod =
      ((List.ofFn (fun t : Fin n => immLayer K n t)).map F).prod at h
    rw [hm] at h
    exact congrArg (fun M => M ⟨0, hn⟩ ⟨0, hn⟩) h
  · simp [imm, hn]

end Problem335

end

end OAI
