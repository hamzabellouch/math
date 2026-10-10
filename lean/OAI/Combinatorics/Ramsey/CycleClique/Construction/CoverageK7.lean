import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK7
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k7t3_cover4 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 7 3 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p0, Certificates.k7t3p0_check⟩

private theorem k7t3_cover3 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 7 3 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k7t3_cover4

private theorem k7t3_cover5 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 7 3 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p1, Certificates.k7t3p1_check⟩

private theorem k7t3_cover6 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 7 3 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p2, Certificates.k7t3p2_check⟩

private theorem k7t3_cover7 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 7 3 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p3, Certificates.k7t3p3_check⟩

private theorem k7t3_cover8 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 7 3 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p4, Certificates.k7t3p4_check⟩

private theorem k7t3_cover2 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 7 3 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t3_cover3
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k7t3_cover5
        · exact by
            intro _
            exact k7t3_cover6
        · exact by
            intro _
            exact k7t3_cover7
        · exact by
            intro _
            exact k7t3_cover8

private theorem k7t3_cover9 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 7 3 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k7t3_cover10 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 7 3 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p5, Certificates.k7t3p5_check⟩

private theorem k7t3_cover11 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 7 3 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p6, Certificates.k7t3p6_check⟩

private theorem k7t3_cover12 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 7 3 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p7, Certificates.k7t3p7_check⟩

private theorem k7t3_cover13 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 7 3 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k7t3_cover14 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 7 3 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t3p8, Certificates.k7t3p8_check⟩

private theorem k7t3_cover15 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 7 3 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k7t3_cover16 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 7 3 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k7t3_cover1 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 7 3 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t3_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t3_cover9
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k7t3_cover10
              · exact by
                  intro _
                  exact k7t3_cover11
              · exact by
                  intro _
                  exact k7t3_cover12
        · exact by
            constructor
            · exact by
                intro _
                exact k7t3_cover13
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k7t3_cover14
        · exact by
            constructor
            · exact by
                intro _
                exact k7t3_cover15
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k7t3_cover16
            · intro q
              exact Fin.elim0 q

theorem coverage_k7_t3 :
    ∀ P ∈ pathPatterns 3 4, HasCheckedCertificate 7 3 P :=
  k7t3_cover1

private theorem k7t4_cover5 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 7 4 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p0, Certificates.k7t4p0_check⟩

private theorem k7t4_cover4 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 7 4 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k7t4_cover5

private theorem k7t4_cover6 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 7 4 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p1, Certificates.k7t4p1_check⟩

private theorem k7t4_cover7 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 7 4 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p2, Certificates.k7t4p2_check⟩

private theorem k7t4_cover8 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 7 4 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p3, Certificates.k7t4p3_check⟩

private theorem k7t4_cover3 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 7 4 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t4_cover4
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k7t4_cover6
        · exact by
            intro _
            exact k7t4_cover7
        · exact by
            intro _
            exact k7t4_cover8

private theorem k7t4_cover9 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 7 4 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k7t4_cover10 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 7 4 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p4, Certificates.k7t4p4_check⟩

private theorem k7t4_cover11 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 7 4 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p5, Certificates.k7t4p5_check⟩

private theorem k7t4_cover12 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 7 4 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k7t4_cover13 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 7 4 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k7t4_cover2 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 7 4 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t4_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover9
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k7t4_cover10
              · exact by
                  intro _
                  exact k7t4_cover11
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover12
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover13
            · intro q
              exact Fin.elim0 q

private theorem k7t4_cover15 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 7 4 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p6, Certificates.k7t4p6_check⟩

private theorem k7t4_cover16 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 7 4 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p7, Certificates.k7t4p7_check⟩

private theorem k7t4_cover14 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 7 4 ([[1]] ++ P) := by
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
            exact k7t4_cover15
        · exact by
            intro _
            exact k7t4_cover16

private theorem k7t4_cover17 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 7 4 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k7t4_cover18 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 7 4 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t4p8, Certificates.k7t4p8_check⟩

private theorem k7t4_cover19 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 7 4 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k7t4_cover20 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 7 4 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)

private theorem k7t4_cover21 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 7 4 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t4_cover1 : ∀ P ∈ pathPatterns 4 3 [], HasCheckedCertificate 7 4 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t4_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover14
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k7t4_cover17
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k7t4_cover18
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k7t4_cover19
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover20
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t4_cover21
            · intro q
              exact Fin.elim0 q

theorem coverage_k7_t4 :
    ∀ P ∈ pathPatterns 4 3, HasCheckedCertificate 7 4 P :=
  k7t4_cover1

private theorem k7t5_cover6 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 7 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t5p0, Certificates.k7t5p0_check⟩

private theorem k7t5_cover5 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 7 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k7t5_cover6

private theorem k7t5_cover7 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 7 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t5p1, Certificates.k7t5p1_check⟩

private theorem k7t5_cover8 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 7 5 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t5p2, Certificates.k7t5p2_check⟩

private theorem k7t5_cover4 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 7 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t5_cover5
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k7t5_cover7
        · exact by
            intro _
            exact k7t5_cover8

private theorem k7t5_cover9 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 7 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k7t5_cover10 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 7 5 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t5p3, Certificates.k7t5p3_check⟩

private theorem k7t5_cover11 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 7 5 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k7t5_cover3 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 7 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t5_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover9
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k7t5_cover10
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover11
            · intro q
              exact Fin.elim0 q

private theorem k7t5_cover13 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 7 5 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t5p4, Certificates.k7t5p4_check⟩

private theorem k7t5_cover12 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 7 5 ([[], [1]] ++ P) := by
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
            exact k7t5_cover13

private theorem k7t5_cover14 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 7 5 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k7t5_cover15 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 7 5 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t5_cover2 : ∀ P ∈ pathPatterns 4 2 [], HasCheckedCertificate 7 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t5_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover12
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k7t5_cover14
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover15
            · intro q
              exact Fin.elim0 q

private theorem k7t5_cover17 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 7 5 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k7t5_cover16 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 7 5 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover17
            · intro q
              exact Fin.elim0 q

private theorem k7t5_cover18 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 7 5 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t5_cover19 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 7 5 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t5_cover1 : ∀ P ∈ pathPatterns 5 2 [], HasCheckedCertificate 7 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t5_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover16
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k7t5_cover18
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t5_cover19
            · intro q
              exact Fin.elim0 q

theorem coverage_k7_t5 :
    ∀ P ∈ pathPatterns 5 2, HasCheckedCertificate 7 5 P :=
  k7t5_cover1

private theorem k7t6_cover7 : ∀ P ∈ pathPatterns 0 1 [], HasCheckedCertificate 7 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t6p0, Certificates.k7t6p0_check⟩

private theorem k7t6_cover6 : ∀ P ∈ pathPatterns 1 1 [], HasCheckedCertificate 7 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k7t6_cover7

private theorem k7t6_cover8 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 7 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t6p1, Certificates.k7t6p1_check⟩

private theorem k7t6_cover5 : ∀ P ∈ pathPatterns 2 1 [], HasCheckedCertificate 7 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t6_cover6
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k7t6_cover8

private theorem k7t6_cover9 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 7 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k7t6_cover4 : ∀ P ∈ pathPatterns 3 1 [], HasCheckedCertificate 7 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t6_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t6_cover9
            · intro q
              exact Fin.elim0 q

private theorem k7t6_cover10 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 7 6 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t6_cover3 : ∀ P ∈ pathPatterns 4 1 [], HasCheckedCertificate 7 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t6_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t6_cover10
            · intro q
              exact Fin.elim0 q

private theorem k7t6_cover11 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 7 6 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t6_cover2 : ∀ P ∈ pathPatterns 5 1 [], HasCheckedCertificate 7 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t6_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t6_cover11
            · intro q
              exact Fin.elim0 q

private theorem k7t6_cover12 : ∀ P ∈ pathPatterns 4 0 [1], HasCheckedCertificate 7 6 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k7t6_cover1 : ∀ P ∈ pathPatterns 6 1 [], HasCheckedCertificate 7 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t6_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k7t6_cover12
            · intro q
              exact Fin.elim0 q

theorem coverage_k7_t6 :
    ∀ P ∈ pathPatterns 6 1, HasCheckedCertificate 7 6 P :=
  k7t6_cover1

private theorem k7t7_cover8 : ∀ P ∈ pathPatterns 0 0 [], HasCheckedCertificate 7 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k7t7p0, Certificates.k7t7p0_check⟩

private theorem k7t7_cover7 : ∀ P ∈ pathPatterns 1 0 [], HasCheckedCertificate 7 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k7t7_cover8

private theorem k7t7_cover6 : ∀ P ∈ pathPatterns 2 0 [], HasCheckedCertificate 7 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover7
      · intro q
        exact Fin.elim0 q

private theorem k7t7_cover5 : ∀ P ∈ pathPatterns 3 0 [], HasCheckedCertificate 7 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover6
      · intro q
        exact Fin.elim0 q

private theorem k7t7_cover4 : ∀ P ∈ pathPatterns 4 0 [], HasCheckedCertificate 7 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover5
      · intro q
        exact Fin.elim0 q

private theorem k7t7_cover3 : ∀ P ∈ pathPatterns 5 0 [], HasCheckedCertificate 7 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover4
      · intro q
        exact Fin.elim0 q

private theorem k7t7_cover2 : ∀ P ∈ pathPatterns 6 0 [], HasCheckedCertificate 7 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover3
      · intro q
        exact Fin.elim0 q

private theorem k7t7_cover1 : ∀ P ∈ pathPatterns 7 0 [], HasCheckedCertificate 7 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k7t7_cover2
      · intro q
        exact Fin.elim0 q

theorem coverage_k7_t7 :
    ∀ P ∈ pathPatterns 7 0, HasCheckedCertificate 7 7 P :=
  k7t7_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
