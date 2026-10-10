import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK8
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k8t4_cover5 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 8 4 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p0, Certificates.k8t4p0_check⟩

private theorem k8t4_cover4 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 8 4 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k8t4_cover5

private theorem k8t4_cover6 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 8 4 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p1, Certificates.k8t4p1_check⟩

private theorem k8t4_cover7 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 8 4 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p2, Certificates.k8t4p2_check⟩

private theorem k8t4_cover8 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 8 4 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p3, Certificates.k8t4p3_check⟩

private theorem k8t4_cover9 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 8 4 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p4, Certificates.k8t4p4_check⟩

private theorem k8t4_cover3 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 8 4 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t4_cover4
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k8t4_cover6
        · exact by
            intro _
            exact k8t4_cover7
        · exact by
            intro _
            exact k8t4_cover8
        · exact by
            intro _
            exact k8t4_cover9

private theorem k8t4_cover10 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 8 4 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover11 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 8 4 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p5, Certificates.k8t4p5_check⟩

private theorem k8t4_cover12 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 8 4 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p6, Certificates.k8t4p6_check⟩

private theorem k8t4_cover13 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 8 4 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p7, Certificates.k8t4p7_check⟩

private theorem k8t4_cover14 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 8 4 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover15 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 8 4 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p8, Certificates.k8t4p8_check⟩

private theorem k8t4_cover16 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 8 4 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover17 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 8 4 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover2 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 8 4 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t4_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover10
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k8t4_cover11
              · exact by
                  intro _
                  exact k8t4_cover12
              · exact by
                  intro _
                  exact k8t4_cover13
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover14
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k8t4_cover15
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover16
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover17
            · intro q
              exact Fin.elim0 q

private theorem k8t4_cover19 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 8 4 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p9, Certificates.k8t4p9_check⟩

private theorem k8t4_cover20 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 8 4 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p10, Certificates.k8t4p10_check⟩

private theorem k8t4_cover21 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 8 4 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p11, Certificates.k8t4p11_check⟩

private theorem k8t4_cover18 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 8 4 ([[1]] ++ P) := by
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
            exact k8t4_cover19
        · exact by
            intro _
            exact k8t4_cover20
        · exact by
            intro _
            exact k8t4_cover21

private theorem k8t4_cover22 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 8 4 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover23 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 8 4 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p12, Certificates.k8t4p12_check⟩

private theorem k8t4_cover24 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 8 4 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p13, Certificates.k8t4p13_check⟩

private theorem k8t4_cover25 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 8 4 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover26 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 8 4 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p14, Certificates.k8t4p14_check⟩

private theorem k8t4_cover27 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 8 4 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover29 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 8 4 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t4p15, Certificates.k8t4p15_check⟩

private theorem k8t4_cover28 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 8 4 ([[2]] ++ P) := by
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
        · exact by
            intro _
            exact k8t4_cover29

private theorem k8t4_cover30 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 8 4 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k8t4_cover31 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 8 4 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)

private theorem k8t4_cover32 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 8 4 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t4_cover1 : ∀ P ∈ pathPatterns 4 4 [], HasCheckedCertificate 8 4 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t4_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover18
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t4_cover22
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k8t4_cover23
                    · exact by
                        intro _
                        exact k8t4_cover24
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t4_cover25
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k8t4_cover26
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t4_cover27
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover28
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t4_cover30
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover31
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t4_cover32
            · intro q
              exact Fin.elim0 q

theorem coverage_k8_t4 :
    ∀ P ∈ pathPatterns 4 4, HasCheckedCertificate 8 4 P :=
  k8t4_cover1

private theorem k8t5_cover6 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 8 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p0, Certificates.k8t5p0_check⟩

private theorem k8t5_cover5 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 8 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k8t5_cover6

private theorem k8t5_cover7 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 8 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p1, Certificates.k8t5p1_check⟩

private theorem k8t5_cover8 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 8 5 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p2, Certificates.k8t5p2_check⟩

private theorem k8t5_cover9 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 8 5 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p3, Certificates.k8t5p3_check⟩

private theorem k8t5_cover4 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 8 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t5_cover5
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k8t5_cover7
        · exact by
            intro _
            exact k8t5_cover8
        · exact by
            intro _
            exact k8t5_cover9

private theorem k8t5_cover10 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 8 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover11 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 8 5 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p4, Certificates.k8t5p4_check⟩

private theorem k8t5_cover12 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 8 5 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p5, Certificates.k8t5p5_check⟩

private theorem k8t5_cover13 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 8 5 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover14 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 8 5 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover3 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 8 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t5_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover10
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k8t5_cover11
              · exact by
                  intro _
                  exact k8t5_cover12
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover13
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover14
            · intro q
              exact Fin.elim0 q

private theorem k8t5_cover16 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 8 5 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p6, Certificates.k8t5p6_check⟩

private theorem k8t5_cover17 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 8 5 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p7, Certificates.k8t5p7_check⟩

private theorem k8t5_cover15 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 8 5 ([[], [1]] ++ P) := by
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
            exact k8t5_cover16
        · exact by
            intro _
            exact k8t5_cover17

private theorem k8t5_cover18 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 8 5 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover19 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 8 5 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p8, Certificates.k8t5p8_check⟩

private theorem k8t5_cover20 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 8 5 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover21 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 8 5 ([[], [2]] ++ P) := by
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

private theorem k8t5_cover22 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 8 5 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t5_cover2 : ∀ P ∈ pathPatterns 4 3 [], HasCheckedCertificate 8 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t5_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover15
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t5_cover18
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k8t5_cover19
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t5_cover20
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover21
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
                exact k8t5_cover22
            · intro q
              exact Fin.elim0 q

private theorem k8t5_cover24 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 8 5 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover25 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 8 5 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t5p9, Certificates.k8t5p9_check⟩

private theorem k8t5_cover26 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 8 5 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover23 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 8 5 ([[1]] ++ P) := by
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
                exact k8t5_cover24
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k8t5_cover25
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover26
            · intro q
              exact Fin.elim0 q

private theorem k8t5_cover27 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 8 5 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k8t5_cover28 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 8 5 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k8t5_cover29 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 8 5 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t5_cover30 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 8 5 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k8t5_cover31 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 8 5 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t5_cover1 : ∀ P ∈ pathPatterns 5 3 [], HasCheckedCertificate 8 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t5_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover23
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t5_cover27
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k8t5_cover28
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t5_cover29
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t5_cover30
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
                exact k8t5_cover31
            · intro q
              exact Fin.elim0 q

theorem coverage_k8_t5 :
    ∀ P ∈ pathPatterns 5 3, HasCheckedCertificate 8 5 P :=
  k8t5_cover1

private theorem k8t6_cover7 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 8 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t6p0, Certificates.k8t6p0_check⟩

private theorem k8t6_cover6 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 8 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k8t6_cover7

private theorem k8t6_cover8 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 8 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t6p1, Certificates.k8t6p1_check⟩

private theorem k8t6_cover9 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 8 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t6p2, Certificates.k8t6p2_check⟩

private theorem k8t6_cover5 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 8 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t6_cover6
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k8t6_cover8
        · exact by
            intro _
            exact k8t6_cover9

private theorem k8t6_cover10 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 8 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t6_cover11 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 8 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t6p3, Certificates.k8t6p3_check⟩

private theorem k8t6_cover12 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 8 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k8t6_cover4 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 8 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t6_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover10
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k8t6_cover11
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover12
            · intro q
              exact Fin.elim0 q

private theorem k8t6_cover14 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 8 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t6p4, Certificates.k8t6p4_check⟩

private theorem k8t6_cover13 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 8 6 ([[], [], [1]] ++ P) := by
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
            exact k8t6_cover14

private theorem k8t6_cover15 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 8 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k8t6_cover16 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 8 6 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover3 : ∀ P ∈ pathPatterns 4 2 [], HasCheckedCertificate 8 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t6_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover13
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t6_cover15
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover16
            · intro q
              exact Fin.elim0 q

private theorem k8t6_cover18 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 8 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t6_cover17 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 8 6 ([[], [1]] ++ P) := by
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
                exact k8t6_cover18
            · intro q
              exact Fin.elim0 q

private theorem k8t6_cover19 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 8 6 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover20 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 8 6 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover2 : ∀ P ∈ pathPatterns 5 2 [], HasCheckedCertificate 8 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t6_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover17
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t6_cover19
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover20
            · intro q
              exact Fin.elim0 q

private theorem k8t6_cover22 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 8 6 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover21 : ∀ P ∈ pathPatterns 4 1 [1], HasCheckedCertificate 8 6 ([[1]] ++ P) := by
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
                exact k8t6_cover22
            · intro q
              exact Fin.elim0 q

private theorem k8t6_cover23 : ∀ P ∈ pathPatterns 3 0 [1, 1], HasCheckedCertificate 8 6 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover24 : ∀ P ∈ pathPatterns 4 0 [2], HasCheckedCertificate 8 6 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t6_cover1 : ∀ P ∈ pathPatterns 6 2 [], HasCheckedCertificate 8 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t6_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover21
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k8t6_cover23
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t6_cover24
            · intro q
              exact Fin.elim0 q

theorem coverage_k8_t6 :
    ∀ P ∈ pathPatterns 6 2, HasCheckedCertificate 8 6 P :=
  k8t6_cover1

private theorem k8t7_cover8 : ∀ P ∈ pathPatterns 0 1 [], HasCheckedCertificate 8 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t7p0, Certificates.k8t7p0_check⟩

private theorem k8t7_cover7 : ∀ P ∈ pathPatterns 1 1 [], HasCheckedCertificate 8 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k8t7_cover8

private theorem k8t7_cover9 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 8 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t7p1, Certificates.k8t7p1_check⟩

private theorem k8t7_cover6 : ∀ P ∈ pathPatterns 2 1 [], HasCheckedCertificate 8 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k8t7_cover9

private theorem k8t7_cover10 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 8 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k8t7_cover5 : ∀ P ∈ pathPatterns 3 1 [], HasCheckedCertificate 8 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t7_cover10
            · intro q
              exact Fin.elim0 q

private theorem k8t7_cover11 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 8 7 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t7_cover4 : ∀ P ∈ pathPatterns 4 1 [], HasCheckedCertificate 8 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t7_cover11
            · intro q
              exact Fin.elim0 q

private theorem k8t7_cover12 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 8 7 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t7_cover3 : ∀ P ∈ pathPatterns 5 1 [], HasCheckedCertificate 8 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t7_cover12
            · intro q
              exact Fin.elim0 q

private theorem k8t7_cover13 : ∀ P ∈ pathPatterns 4 0 [1], HasCheckedCertificate 8 7 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t7_cover2 : ∀ P ∈ pathPatterns 6 1 [], HasCheckedCertificate 8 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t7_cover13
            · intro q
              exact Fin.elim0 q

private theorem k8t7_cover14 : ∀ P ∈ pathPatterns 5 0 [1], HasCheckedCertificate 8 7 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k8t7_cover1 : ∀ P ∈ pathPatterns 7 1 [], HasCheckedCertificate 8 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t7_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k8t7_cover14
            · intro q
              exact Fin.elim0 q

theorem coverage_k8_t7 :
    ∀ P ∈ pathPatterns 7 1, HasCheckedCertificate 8 7 P :=
  k8t7_cover1

private theorem k8t8_cover9 : ∀ P ∈ pathPatterns 0 0 [], HasCheckedCertificate 8 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k8t8p0, Certificates.k8t8p0_check⟩

private theorem k8t8_cover8 : ∀ P ∈ pathPatterns 1 0 [], HasCheckedCertificate 8 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k8t8_cover9

private theorem k8t8_cover7 : ∀ P ∈ pathPatterns 2 0 [], HasCheckedCertificate 8 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover8
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover6 : ∀ P ∈ pathPatterns 3 0 [], HasCheckedCertificate 8 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover7
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover5 : ∀ P ∈ pathPatterns 4 0 [], HasCheckedCertificate 8 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover6
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover4 : ∀ P ∈ pathPatterns 5 0 [], HasCheckedCertificate 8 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover5
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover3 : ∀ P ∈ pathPatterns 6 0 [], HasCheckedCertificate 8 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover4
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover2 : ∀ P ∈ pathPatterns 7 0 [], HasCheckedCertificate 8 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover3
      · intro q
        exact Fin.elim0 q

private theorem k8t8_cover1 : ∀ P ∈ pathPatterns 8 0 [], HasCheckedCertificate 8 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k8t8_cover2
      · intro q
        exact Fin.elim0 q

theorem coverage_k8_t8 :
    ∀ P ∈ pathPatterns 8 0, HasCheckedCertificate 8 8 P :=
  k8t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
