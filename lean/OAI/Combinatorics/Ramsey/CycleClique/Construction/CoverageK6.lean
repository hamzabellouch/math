import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK6
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k6t3_cover4 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 6 3 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p0, Certificates.k6t3p0_check⟩

private theorem k6t3_cover3 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 6 3 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k6t3_cover4

private theorem k6t3_cover5 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 6 3 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p1, Certificates.k6t3p1_check⟩

private theorem k6t3_cover6 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 6 3 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p2, Certificates.k6t3p2_check⟩

private theorem k6t3_cover7 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 6 3 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p3, Certificates.k6t3p3_check⟩

private theorem k6t3_cover2 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 6 3 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t3_cover3
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k6t3_cover5
        · exact by
            intro _
            exact k6t3_cover6
        · exact by
            intro _
            exact k6t3_cover7

private theorem k6t3_cover8 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 6 3 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k6t3_cover9 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 6 3 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p4, Certificates.k6t3p4_check⟩

private theorem k6t3_cover10 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 6 3 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t3p5, Certificates.k6t3p5_check⟩

private theorem k6t3_cover11 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 6 3 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k6t3_cover12 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 6 3 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k6t3_cover1 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 6 3 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t3_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t3_cover8
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k6t3_cover9
              · exact by
                  intro _
                  exact k6t3_cover10
        · exact by
            constructor
            · exact by
                intro _
                exact k6t3_cover11
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k6t3_cover12
            · intro q
              exact Fin.elim0 q

theorem coverage_k6_t3 :
    ∀ P ∈ pathPatterns 3 3, HasCheckedCertificate 6 3 P :=
  k6t3_cover1

private theorem k6t4_cover5 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 6 4 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t4p0, Certificates.k6t4p0_check⟩

private theorem k6t4_cover4 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 6 4 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k6t4_cover5

private theorem k6t4_cover6 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 6 4 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t4p1, Certificates.k6t4p1_check⟩

private theorem k6t4_cover7 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 6 4 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t4p2, Certificates.k6t4p2_check⟩

private theorem k6t4_cover3 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 6 4 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t4_cover4
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k6t4_cover6
        · exact by
            intro _
            exact k6t4_cover7

private theorem k6t4_cover8 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 6 4 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k6t4_cover9 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 6 4 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t4p3, Certificates.k6t4p3_check⟩

private theorem k6t4_cover10 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 6 4 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k6t4_cover2 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 6 4 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t4_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t4_cover8
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k6t4_cover9
        · exact by
            constructor
            · exact by
                intro _
                exact k6t4_cover10
            · intro q
              exact Fin.elim0 q

private theorem k6t4_cover12 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 6 4 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t4p4, Certificates.k6t4p4_check⟩

private theorem k6t4_cover11 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 6 4 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k6t4_cover12

private theorem k6t4_cover13 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 6 4 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k6t4_cover14 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 6 4 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k6t4_cover1 : ∀ P ∈ pathPatterns 4 2 [], HasCheckedCertificate 6 4 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t4_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t4_cover11
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k6t4_cover13
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t4_cover14
            · intro q
              exact Fin.elim0 q

theorem coverage_k6_t4 :
    ∀ P ∈ pathPatterns 4 2, HasCheckedCertificate 6 4 P :=
  k6t4_cover1

private theorem k6t5_cover6 : ∀ P ∈ pathPatterns 0 1 [], HasCheckedCertificate 6 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t5p0, Certificates.k6t5p0_check⟩

private theorem k6t5_cover5 : ∀ P ∈ pathPatterns 1 1 [], HasCheckedCertificate 6 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k6t5_cover6

private theorem k6t5_cover7 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 6 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t5p1, Certificates.k6t5p1_check⟩

private theorem k6t5_cover4 : ∀ P ∈ pathPatterns 2 1 [], HasCheckedCertificate 6 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t5_cover5
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k6t5_cover7

private theorem k6t5_cover8 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 6 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k6t5_cover3 : ∀ P ∈ pathPatterns 3 1 [], HasCheckedCertificate 6 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t5_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t5_cover8
            · intro q
              exact Fin.elim0 q

private theorem k6t5_cover9 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 6 5 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k6t5_cover2 : ∀ P ∈ pathPatterns 4 1 [], HasCheckedCertificate 6 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t5_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t5_cover9
            · intro q
              exact Fin.elim0 q

private theorem k6t5_cover10 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 6 5 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k6t5_cover1 : ∀ P ∈ pathPatterns 5 1 [], HasCheckedCertificate 6 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t5_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k6t5_cover10
            · intro q
              exact Fin.elim0 q

theorem coverage_k6_t5 :
    ∀ P ∈ pathPatterns 5 1, HasCheckedCertificate 6 5 P :=
  k6t5_cover1

private theorem k6t6_cover7 : ∀ P ∈ pathPatterns 0 0 [], HasCheckedCertificate 6 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k6t6p0, Certificates.k6t6p0_check⟩

private theorem k6t6_cover6 : ∀ P ∈ pathPatterns 1 0 [], HasCheckedCertificate 6 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k6t6_cover7

private theorem k6t6_cover5 : ∀ P ∈ pathPatterns 2 0 [], HasCheckedCertificate 6 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t6_cover6
      · intro q
        exact Fin.elim0 q

private theorem k6t6_cover4 : ∀ P ∈ pathPatterns 3 0 [], HasCheckedCertificate 6 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t6_cover5
      · intro q
        exact Fin.elim0 q

private theorem k6t6_cover3 : ∀ P ∈ pathPatterns 4 0 [], HasCheckedCertificate 6 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t6_cover4
      · intro q
        exact Fin.elim0 q

private theorem k6t6_cover2 : ∀ P ∈ pathPatterns 5 0 [], HasCheckedCertificate 6 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t6_cover3
      · intro q
        exact Fin.elim0 q

private theorem k6t6_cover1 : ∀ P ∈ pathPatterns 6 0 [], HasCheckedCertificate 6 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k6t6_cover2
      · intro q
        exact Fin.elim0 q

theorem coverage_k6_t6 :
    ∀ P ∈ pathPatterns 6 0, HasCheckedCertificate 6 6 P :=
  k6t6_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
