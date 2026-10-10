import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK9
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k9t4_cover6 : ∀ P ∈ pathPatterns 0 5 [], HasCheckedCertificate 9 4 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p0, Certificates.k9t4p0_check⟩

private theorem k9t4_cover5 : ∀ P ∈ pathPatterns 1 5 [], HasCheckedCertificate 9 4 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k9t4_cover6

private theorem k9t4_cover7 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 9 4 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p1, Certificates.k9t4p1_check⟩

private theorem k9t4_cover8 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 9 4 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p2, Certificates.k9t4p2_check⟩

private theorem k9t4_cover9 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 9 4 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p3, Certificates.k9t4p3_check⟩

private theorem k9t4_cover10 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 9 4 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p4, Certificates.k9t4p4_check⟩

private theorem k9t4_cover11 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 9 4 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p5, Certificates.k9t4p5_check⟩

private theorem k9t4_cover4 : ∀ P ∈ pathPatterns 2 5 [], HasCheckedCertificate 9 4 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t4_cover5
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k9t4_cover7
        · exact by
            intro _
            exact k9t4_cover8
        · exact by
            intro _
            exact k9t4_cover9
        · exact by
            intro _
            exact k9t4_cover10
        · exact by
            intro _
            exact k9t4_cover11

private theorem k9t4_cover12 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 9 4 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover13 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 9 4 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p6, Certificates.k9t4p6_check⟩

private theorem k9t4_cover14 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 9 4 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p7, Certificates.k9t4p7_check⟩

private theorem k9t4_cover15 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 9 4 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p8, Certificates.k9t4p8_check⟩

private theorem k9t4_cover16 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 9 4 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p9, Certificates.k9t4p9_check⟩

private theorem k9t4_cover17 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 9 4 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover18 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 9 4 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p10, Certificates.k9t4p10_check⟩

private theorem k9t4_cover19 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 9 4 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p11, Certificates.k9t4p11_check⟩

private theorem k9t4_cover20 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 9 4 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover21 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 9 4 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover22 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 9 4 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover3 : ∀ P ∈ pathPatterns 3 5 [], HasCheckedCertificate 9 4 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t4_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t4_cover12
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t4_cover13
              · exact by
                  intro _
                  exact k9t4_cover14
              · exact by
                  intro _
                  exact k9t4_cover15
              · exact by
                  intro _
                  exact k9t4_cover16
        · exact by
            constructor
            · exact by
                intro _
                exact k9t4_cover17
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k9t4_cover18
              · exact by
                  intro _
                  exact k9t4_cover19
        · exact by
            constructor
            · exact by
                intro _
                exact k9t4_cover20
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t4_cover21
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t4_cover22
            · intro q
              exact Fin.elim0 q

private theorem k9t4_cover24 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 9 4 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p12, Certificates.k9t4p12_check⟩

private theorem k9t4_cover25 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 9 4 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p13, Certificates.k9t4p13_check⟩

private theorem k9t4_cover26 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 9 4 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p14, Certificates.k9t4p14_check⟩

private theorem k9t4_cover27 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 9 4 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p15, Certificates.k9t4p15_check⟩

private theorem k9t4_cover23 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 9 4 ([[1]] ++ P) := by
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
            exact k9t4_cover24
        · exact by
            intro _
            exact k9t4_cover25
        · exact by
            intro _
            exact k9t4_cover26
        · exact by
            intro _
            exact k9t4_cover27

private theorem k9t4_cover28 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 9 4 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover29 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 9 4 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p16, Certificates.k9t4p16_check⟩

private theorem k9t4_cover30 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 9 4 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p17, Certificates.k9t4p17_check⟩

private theorem k9t4_cover31 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 9 4 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p18, Certificates.k9t4p18_check⟩

private theorem k9t4_cover32 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 9 4 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover33 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 9 4 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p19, Certificates.k9t4p19_check⟩

private theorem k9t4_cover34 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 9 4 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p20, Certificates.k9t4p20_check⟩

private theorem k9t4_cover35 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 9 4 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover36 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 9 4 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p21, Certificates.k9t4p21_check⟩

private theorem k9t4_cover37 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 9 4 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover39 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 9 4 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p22, Certificates.k9t4p22_check⟩

private theorem k9t4_cover40 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 9 4 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p23, Certificates.k9t4p23_check⟩

private theorem k9t4_cover38 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 9 4 ([[2]] ++ P) := by
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
            exact k9t4_cover39
        · exact by
            intro _
            exact k9t4_cover40

private theorem k9t4_cover41 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 9 4 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t4p24, Certificates.k9t4p24_check⟩

private theorem k9t4_cover42 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 9 4 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover43 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 9 4 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k9t4_cover44 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 9 4 ([[3]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)

private theorem k9t4_cover45 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 9 4 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)

private theorem k9t4_cover46 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 9 4 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t4_seq2 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 9 4 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k9t4_cover3
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k9t4_cover23
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover28
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k9t4_cover29
                · exact by
                    intro _
                    exact k9t4_cover30
                · exact by
                    intro _
                    exact k9t4_cover31
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover32
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k9t4_cover33
                · exact by
                    intro _
                    exact k9t4_cover34
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover35
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k9t4_cover36
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover37
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k9t4_cover38
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
                    intro _
                    exact k9t4_cover41
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover42
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k9t4_cover43
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k9t4_cover44
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k9t4_cover45
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k9t4_cover46
        · intro q
          exact Fin.elim0 q

private theorem k9t4_cover1 : ∀ P ∈ pathPatterns 4 5 [], HasCheckedCertificate 9 4 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k9t4_seq2


theorem coverage_k9_t4 :
    ∀ P ∈ pathPatterns 4 5, HasCheckedCertificate 9 4 P :=
  k9t4_cover1

private theorem k9t5_cover6 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 9 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p0, Certificates.k9t5p0_check⟩

private theorem k9t5_cover5 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 9 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k9t5_cover6

private theorem k9t5_cover7 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 9 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p1, Certificates.k9t5p1_check⟩

private theorem k9t5_cover8 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 9 5 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p2, Certificates.k9t5p2_check⟩

private theorem k9t5_cover9 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 9 5 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p3, Certificates.k9t5p3_check⟩

private theorem k9t5_cover10 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 9 5 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p4, Certificates.k9t5p4_check⟩

private theorem k9t5_cover4 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 9 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t5_cover5
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k9t5_cover7
        · exact by
            intro _
            exact k9t5_cover8
        · exact by
            intro _
            exact k9t5_cover9
        · exact by
            intro _
            exact k9t5_cover10

private theorem k9t5_cover11 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 9 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover12 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 9 5 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p5, Certificates.k9t5p5_check⟩

private theorem k9t5_cover13 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 9 5 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p6, Certificates.k9t5p6_check⟩

private theorem k9t5_cover14 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 9 5 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p7, Certificates.k9t5p7_check⟩

private theorem k9t5_cover15 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 9 5 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover16 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 9 5 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p8, Certificates.k9t5p8_check⟩

private theorem k9t5_cover17 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 9 5 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover18 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 9 5 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover3 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 9 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t5_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover11
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t5_cover12
              · exact by
                  intro _
                  exact k9t5_cover13
              · exact by
                  intro _
                  exact k9t5_cover14
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover15
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k9t5_cover16
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover17
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover18
            · intro q
              exact Fin.elim0 q

private theorem k9t5_cover20 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 9 5 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p9, Certificates.k9t5p9_check⟩

private theorem k9t5_cover21 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 9 5 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p10, Certificates.k9t5p10_check⟩

private theorem k9t5_cover22 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 9 5 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p11, Certificates.k9t5p11_check⟩

private theorem k9t5_cover19 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 9 5 ([[], [1]] ++ P) := by
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
            exact k9t5_cover20
        · exact by
            intro _
            exact k9t5_cover21
        · exact by
            intro _
            exact k9t5_cover22

private theorem k9t5_cover23 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 9 5 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover24 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 9 5 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p12, Certificates.k9t5p12_check⟩

private theorem k9t5_cover25 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 9 5 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p13, Certificates.k9t5p13_check⟩

private theorem k9t5_cover26 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 9 5 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover27 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 9 5 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p14, Certificates.k9t5p14_check⟩

private theorem k9t5_cover28 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 9 5 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover30 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 9 5 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p15, Certificates.k9t5p15_check⟩

private theorem k9t5_cover29 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 9 5 ([[], [2]] ++ P) := by
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
            exact k9t5_cover30

private theorem k9t5_cover31 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 9 5 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover32 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 9 5 ([[], [3]] ++ P) := by
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

private theorem k9t5_cover33 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 9 5 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t5_cover2 : ∀ P ∈ pathPatterns 4 4 [], HasCheckedCertificate 9 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t5_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover19
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover23
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k9t5_cover24
                    · exact by
                        intro _
                        exact k9t5_cover25
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover26
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k9t5_cover27
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover28
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover29
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
                      exact k9t5_cover31
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover32
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
                exact k9t5_cover33
            · intro q
              exact Fin.elim0 q

private theorem k9t5_cover35 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 9 5 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover36 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 9 5 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p16, Certificates.k9t5p16_check⟩

private theorem k9t5_cover37 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 9 5 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p17, Certificates.k9t5p17_check⟩

private theorem k9t5_cover38 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 9 5 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover39 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 9 5 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover34 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 9 5 ([[1]] ++ P) := by
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
                exact k9t5_cover35
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t5_cover36
              · exact by
                  intro _
                  exact k9t5_cover37
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover38
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover39
            · intro q
              exact Fin.elim0 q

private theorem k9t5_cover41 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 9 5 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p18, Certificates.k9t5p18_check⟩

private theorem k9t5_cover40 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 9 5 ([[1, 1]] ++ P) := by
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
        · exact by
            intro _
            exact k9t5_cover41

private theorem k9t5_cover42 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 9 5 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover43 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 9 5 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t5p19, Certificates.k9t5p19_check⟩

private theorem k9t5_cover44 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 9 5 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover45 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 9 5 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k9t5_cover46 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 9 5 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover47 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 9 5 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t5_cover49 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 9 5 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t5_cover48 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 9 5 ([[2]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover49
            · intro q
              exact Fin.elim0 q

private theorem k9t5_cover50 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 9 5 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t5_cover51 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 9 5 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k9t5_cover52 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 9 5 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t5_cover1 : ∀ P ∈ pathPatterns 5 4 [], HasCheckedCertificate 9 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t5_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover34
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover40
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k9t5_cover42
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k9t5_cover43
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k9t5_cover44
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover45
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k9t5_cover46
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover47
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover48
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t5_cover50
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t5_cover51
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
                exact k9t5_cover52
            · intro q
              exact Fin.elim0 q

theorem coverage_k9_t5 :
    ∀ P ∈ pathPatterns 5 4, HasCheckedCertificate 9 5 P :=
  k9t5_cover1

private theorem k9t6_cover7 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 9 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p0, Certificates.k9t6p0_check⟩

private theorem k9t6_cover6 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 9 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k9t6_cover7

private theorem k9t6_cover8 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 9 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p1, Certificates.k9t6p1_check⟩

private theorem k9t6_cover9 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 9 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p2, Certificates.k9t6p2_check⟩

private theorem k9t6_cover10 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 9 6 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p3, Certificates.k9t6p3_check⟩

private theorem k9t6_cover5 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 9 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t6_cover6
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k9t6_cover8
        · exact by
            intro _
            exact k9t6_cover9
        · exact by
            intro _
            exact k9t6_cover10

private theorem k9t6_cover11 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 9 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover12 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 9 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p4, Certificates.k9t6p4_check⟩

private theorem k9t6_cover13 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 9 6 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p5, Certificates.k9t6p5_check⟩

private theorem k9t6_cover14 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 9 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover15 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 9 6 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover4 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 9 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t6_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover11
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t6_cover12
              · exact by
                  intro _
                  exact k9t6_cover13
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover14
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover15
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover17 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 9 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p6, Certificates.k9t6p6_check⟩

private theorem k9t6_cover18 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 9 6 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p7, Certificates.k9t6p7_check⟩

private theorem k9t6_cover16 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 9 6 ([[], [], [1]] ++ P) := by
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
            exact k9t6_cover17
        · exact by
            intro _
            exact k9t6_cover18

private theorem k9t6_cover19 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 9 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover20 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 9 6 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p8, Certificates.k9t6p8_check⟩

private theorem k9t6_cover21 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 9 6 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover22 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 9 6 ([[], [], [2]] ++ P) := by
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

private theorem k9t6_cover23 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 9 6 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover3 : ∀ P ∈ pathPatterns 4 3 [], HasCheckedCertificate 9 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t6_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover16
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover19
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k9t6_cover20
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover21
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover22
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
                exact k9t6_cover23
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover25 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 9 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover26 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 9 6 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p9, Certificates.k9t6p9_check⟩

private theorem k9t6_cover27 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 9 6 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover24 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 9 6 ([[], [1]] ++ P) := by
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
                exact k9t6_cover25
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t6_cover26
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover27
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover28 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 9 6 ([[], [1, 1]] ++ P) := by
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

private theorem k9t6_cover29 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 9 6 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover30 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 9 6 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover31 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 9 6 ([[], [2]] ++ P) := by
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

private theorem k9t6_cover32 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 9 6 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover2 : ∀ P ∈ pathPatterns 5 3 [], HasCheckedCertificate 9 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t6_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover24
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover28
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k9t6_cover29
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover30
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover31
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
                exact k9t6_cover32
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover35 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 9 6 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t6p10, Certificates.k9t6p10_check⟩

private theorem k9t6_cover34 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 9 6 ([[1], [1]] ++ P) := by
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
            exact k9t6_cover35

private theorem k9t6_cover36 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 9 6 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t6_cover37 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 9 6 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover33 : ∀ P ∈ pathPatterns 4 2 [1], HasCheckedCertificate 9 6 ([[1]] ++ P) := by
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
                exact k9t6_cover34
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover36
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover37
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover38 : ∀ P ∈ pathPatterns 3 1 [1, 1], HasCheckedCertificate 9 6 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k9t6_cover39 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1], HasCheckedCertificate 9 6 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover40 : ∀ P ∈ pathPatterns 3 0 [1, 2], HasCheckedCertificate 9 6 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover41 : ∀ P ∈ pathPatterns 4 1 [2], HasCheckedCertificate 9 6 ([[2]] ++ P) := by
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

private theorem k9t6_cover42 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 9 6 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t6_cover1 : ∀ P ∈ pathPatterns 6 3 [], HasCheckedCertificate 9 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t6_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover33
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover38
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k9t6_cover39
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t6_cover40
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t6_cover41
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
                exact k9t6_cover42
            · intro q
              exact Fin.elim0 q

theorem coverage_k9_t6 :
    ∀ P ∈ pathPatterns 6 3, HasCheckedCertificate 9 6 P :=
  k9t6_cover1

private theorem k9t7_cover8 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 9 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t7p0, Certificates.k9t7p0_check⟩

private theorem k9t7_cover7 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 9 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k9t7_cover8

private theorem k9t7_cover9 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 9 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t7p1, Certificates.k9t7p1_check⟩

private theorem k9t7_cover10 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 9 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t7p2, Certificates.k9t7p2_check⟩

private theorem k9t7_cover6 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 9 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k9t7_cover9
        · exact by
            intro _
            exact k9t7_cover10

private theorem k9t7_cover11 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 9 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t7_cover12 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 9 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t7p3, Certificates.k9t7p3_check⟩

private theorem k9t7_cover13 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 9 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k9t7_cover5 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 9 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover11
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k9t7_cover12
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover13
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover15 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 9 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t7p4, Certificates.k9t7p4_check⟩

private theorem k9t7_cover14 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 9 7 ([[], [], [], [1]] ++ P) := by
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
            exact k9t7_cover15

private theorem k9t7_cover16 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 9 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k9t7_cover17 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 9 7 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover4 : ∀ P ∈ pathPatterns 4 2 [], HasCheckedCertificate 9 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover14
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t7_cover16
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover17
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover19 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 9 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t7_cover18 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 9 7 ([[], [], [1]] ++ P) := by
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
                exact k9t7_cover19
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover20 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 9 7 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover21 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 9 7 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover3 : ∀ P ∈ pathPatterns 5 2 [], HasCheckedCertificate 9 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover18
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t7_cover20
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover21
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover23 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 9 7 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover22 : ∀ P ∈ pathPatterns 4 1 [1], HasCheckedCertificate 9 7 ([[], [1]] ++ P) := by
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
                exact k9t7_cover23
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover24 : ∀ P ∈ pathPatterns 3 0 [1, 1], HasCheckedCertificate 9 7 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover25 : ∀ P ∈ pathPatterns 4 0 [2], HasCheckedCertificate 9 7 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover2 : ∀ P ∈ pathPatterns 6 2 [], HasCheckedCertificate 9 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover22
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t7_cover24
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover25
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover27 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 9 7 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover26 : ∀ P ∈ pathPatterns 5 1 [1], HasCheckedCertificate 9 7 ([[1]] ++ P) := by
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
                exact k9t7_cover27
            · intro q
              exact Fin.elim0 q

private theorem k9t7_cover28 : ∀ P ∈ pathPatterns 4 0 [1, 1], HasCheckedCertificate 9 7 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover29 : ∀ P ∈ pathPatterns 5 0 [2], HasCheckedCertificate 9 7 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t7_cover1 : ∀ P ∈ pathPatterns 7 2 [], HasCheckedCertificate 9 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t7_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover26
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k9t7_cover28
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t7_cover29
            · intro q
              exact Fin.elim0 q

theorem coverage_k9_t7 :
    ∀ P ∈ pathPatterns 7 2, HasCheckedCertificate 9 7 P :=
  k9t7_cover1

private theorem k9t8_cover9 : ∀ P ∈ pathPatterns 0 1 [], HasCheckedCertificate 9 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t8p0, Certificates.k9t8p0_check⟩

private theorem k9t8_cover8 : ∀ P ∈ pathPatterns 1 1 [], HasCheckedCertificate 9 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k9t8_cover9

private theorem k9t8_cover10 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 9 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k9t8p1, Certificates.k9t8p1_check⟩

private theorem k9t8_cover7 : ∀ P ∈ pathPatterns 2 1 [], HasCheckedCertificate 9 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover8
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k9t8_cover10

private theorem k9t8_cover11 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 9 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k9t8_cover6 : ∀ P ∈ pathPatterns 3 1 [], HasCheckedCertificate 9 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover7
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover11
            · intro q
              exact Fin.elim0 q

private theorem k9t8_cover12 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 9 8 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t8_cover5 : ∀ P ∈ pathPatterns 4 1 [], HasCheckedCertificate 9 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover12
            · intro q
              exact Fin.elim0 q

private theorem k9t8_cover13 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 9 8 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t8_cover4 : ∀ P ∈ pathPatterns 5 1 [], HasCheckedCertificate 9 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover13
            · intro q
              exact Fin.elim0 q

private theorem k9t8_cover14 : ∀ P ∈ pathPatterns 4 0 [1], HasCheckedCertificate 9 8 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t8_cover3 : ∀ P ∈ pathPatterns 6 1 [], HasCheckedCertificate 9 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover14
            · intro q
              exact Fin.elim0 q

private theorem k9t8_cover15 : ∀ P ∈ pathPatterns 5 0 [1], HasCheckedCertificate 9 8 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t8_cover2 : ∀ P ∈ pathPatterns 7 1 [], HasCheckedCertificate 9 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover15
            · intro q
              exact Fin.elim0 q

private theorem k9t8_cover16 : ∀ P ∈ pathPatterns 6 0 [1], HasCheckedCertificate 9 8 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k9t8_cover1 : ∀ P ∈ pathPatterns 8 1 [], HasCheckedCertificate 9 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k9t8_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k9t8_cover16
            · intro q
              exact Fin.elim0 q

theorem coverage_k9_t8 :
    ∀ P ∈ pathPatterns 8 1, HasCheckedCertificate 9 8 P :=
  k9t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
