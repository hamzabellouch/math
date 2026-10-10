import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK5
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k5t3_cover4 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 5 3 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t3p0, Certificates.k5t3p0_check⟩

private theorem k5t3_cover3 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 5 3 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k5t3_cover4

private theorem k5t3_cover5 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 5 3 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t3p1, Certificates.k5t3p1_check⟩

private theorem k5t3_cover6 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 5 3 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t3p2, Certificates.k5t3p2_check⟩

private theorem k5t3_cover2 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 5 3 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t3_cover3
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k5t3_cover5
        · exact by
            intro _
            exact k5t3_cover6

private theorem k5t3_cover7 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 5 3 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k5t3_cover8 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 5 3 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t3p3, Certificates.k5t3p3_check⟩

private theorem k5t3_cover9 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 5 3 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k5t3_cover1 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 5 3 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t3_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k5t3_cover7
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k5t3_cover8
        · exact by
            constructor
            · exact by
                intro _
                exact k5t3_cover9
            · intro q
              exact Fin.elim0 q

theorem coverage_k5_t3 :
    ∀ P ∈ pathPatterns 3 2, HasCheckedCertificate 5 3 P :=
  k5t3_cover1

private theorem k5t4_cover5 : ∀ P ∈ pathPatterns 0 1 [], HasCheckedCertificate 5 4 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t4p0, Certificates.k5t4p0_check⟩

private theorem k5t4_cover4 : ∀ P ∈ pathPatterns 1 1 [], HasCheckedCertificate 5 4 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k5t4_cover5

private theorem k5t4_cover6 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 5 4 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t4p1, Certificates.k5t4p1_check⟩

private theorem k5t4_cover3 : ∀ P ∈ pathPatterns 2 1 [], HasCheckedCertificate 5 4 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t4_cover4
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k5t4_cover6

private theorem k5t4_cover7 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 5 4 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k5t4_cover2 : ∀ P ∈ pathPatterns 3 1 [], HasCheckedCertificate 5 4 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t4_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k5t4_cover7
            · intro q
              exact Fin.elim0 q

private theorem k5t4_cover8 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 5 4 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k5t4_cover1 : ∀ P ∈ pathPatterns 4 1 [], HasCheckedCertificate 5 4 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t4_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k5t4_cover8
            · intro q
              exact Fin.elim0 q

theorem coverage_k5_t4 :
    ∀ P ∈ pathPatterns 4 1, HasCheckedCertificate 5 4 P :=
  k5t4_cover1

private theorem k5t5_cover6 : ∀ P ∈ pathPatterns 0 0 [], HasCheckedCertificate 5 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k5t5p0, Certificates.k5t5p0_check⟩

private theorem k5t5_cover5 : ∀ P ∈ pathPatterns 1 0 [], HasCheckedCertificate 5 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k5t5_cover6

private theorem k5t5_cover4 : ∀ P ∈ pathPatterns 2 0 [], HasCheckedCertificate 5 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t5_cover5
      · intro q
        exact Fin.elim0 q

private theorem k5t5_cover3 : ∀ P ∈ pathPatterns 3 0 [], HasCheckedCertificate 5 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t5_cover4
      · intro q
        exact Fin.elim0 q

private theorem k5t5_cover2 : ∀ P ∈ pathPatterns 4 0 [], HasCheckedCertificate 5 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t5_cover3
      · intro q
        exact Fin.elim0 q

private theorem k5t5_cover1 : ∀ P ∈ pathPatterns 5 0 [], HasCheckedCertificate 5 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k5t5_cover2
      · intro q
        exact Fin.elim0 q

theorem coverage_k5_t5 :
    ∀ P ∈ pathPatterns 5 0, HasCheckedCertificate 5 5 P :=
  k5t5_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
