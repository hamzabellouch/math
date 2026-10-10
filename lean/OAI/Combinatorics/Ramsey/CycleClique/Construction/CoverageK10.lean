import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK10
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k10t5_cover8 : ∀ P ∈ pathPatterns 0 5 [], HasCheckedCertificate 10 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p0, Certificates.k10t5p0_check⟩

private theorem k10t5_cover7 : ∀ P ∈ pathPatterns 1 5 [], HasCheckedCertificate 10 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k10t5_cover8

private theorem k10t5_cover9 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 10 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p1, Certificates.k10t5p1_check⟩

private theorem k10t5_cover10 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 10 5 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p2, Certificates.k10t5p2_check⟩

private theorem k10t5_cover11 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 10 5 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p3, Certificates.k10t5p3_check⟩

private theorem k10t5_cover12 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 10 5 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p4, Certificates.k10t5p4_check⟩

private theorem k10t5_cover13 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 10 5 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p5, Certificates.k10t5p5_check⟩

private theorem k10t5_cover6 : ∀ P ∈ pathPatterns 2 5 [], HasCheckedCertificate 10 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t5_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k10t5_cover9
        · exact by
            intro _
            exact k10t5_cover10
        · exact by
            intro _
            exact k10t5_cover11
        · exact by
            intro _
            exact k10t5_cover12
        · exact by
            intro _
            exact k10t5_cover13

private theorem k10t5_cover14 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 10 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover15 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 10 5 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p6, Certificates.k10t5p6_check⟩

private theorem k10t5_cover16 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 10 5 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p7, Certificates.k10t5p7_check⟩

private theorem k10t5_cover17 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 10 5 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p8, Certificates.k10t5p8_check⟩

private theorem k10t5_cover18 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 10 5 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p9, Certificates.k10t5p9_check⟩

private theorem k10t5_cover19 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 10 5 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover20 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 10 5 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p10, Certificates.k10t5p10_check⟩

private theorem k10t5_cover21 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 10 5 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p11, Certificates.k10t5p11_check⟩

private theorem k10t5_cover22 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 10 5 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover23 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 10 5 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover24 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 10 5 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover5 : ∀ P ∈ pathPatterns 3 5 [], HasCheckedCertificate 10 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t5_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover14
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t5_cover15
              · exact by
                  intro _
                  exact k10t5_cover16
              · exact by
                  intro _
                  exact k10t5_cover17
              · exact by
                  intro _
                  exact k10t5_cover18
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover19
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k10t5_cover20
              · exact by
                  intro _
                  exact k10t5_cover21
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover22
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
                exact k10t5_cover23
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover24
            · intro q
              exact Fin.elim0 q

private theorem k10t5_cover26 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 10 5 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p12, Certificates.k10t5p12_check⟩

private theorem k10t5_cover27 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 10 5 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p13, Certificates.k10t5p13_check⟩

private theorem k10t5_cover28 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 10 5 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p14, Certificates.k10t5p14_check⟩

private theorem k10t5_cover29 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 10 5 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p15, Certificates.k10t5p15_check⟩

private theorem k10t5_cover25 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 10 5 ([[], [1]] ++ P) := by
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
            exact k10t5_cover26
        · exact by
            intro _
            exact k10t5_cover27
        · exact by
            intro _
            exact k10t5_cover28
        · exact by
            intro _
            exact k10t5_cover29

private theorem k10t5_cover30 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 10 5 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover31 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 10 5 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p16, Certificates.k10t5p16_check⟩

private theorem k10t5_cover32 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 10 5 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p17, Certificates.k10t5p17_check⟩

private theorem k10t5_cover33 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 10 5 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p18, Certificates.k10t5p18_check⟩

private theorem k10t5_cover34 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 10 5 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover35 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 10 5 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p19, Certificates.k10t5p19_check⟩

private theorem k10t5_cover36 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 10 5 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p20, Certificates.k10t5p20_check⟩

private theorem k10t5_cover37 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 10 5 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover38 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 10 5 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p21, Certificates.k10t5p21_check⟩

private theorem k10t5_cover39 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 10 5 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover41 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 10 5 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p22, Certificates.k10t5p22_check⟩

private theorem k10t5_cover42 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 10 5 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p23, Certificates.k10t5p23_check⟩

private theorem k10t5_cover40 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 10 5 ([[], [2]] ++ P) := by
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
            exact k10t5_cover41
        · exact by
            intro _
            exact k10t5_cover42

private theorem k10t5_cover43 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 10 5 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p24, Certificates.k10t5p24_check⟩

private theorem k10t5_cover44 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 10 5 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover45 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 10 5 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover46 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 10 5 ([[], [3]] ++ P) := by
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

private theorem k10t5_cover47 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 10 5 ([[], [4]] ++ P) := by
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

private theorem k10t5_cover48 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 10 5 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t5_seq4 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 10 5 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k10t5_cover5
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover25
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover30
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k10t5_cover31
                · exact by
                    intro _
                    exact k10t5_cover32
                · exact by
                    intro _
                    exact k10t5_cover33
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover34
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k10t5_cover35
                · exact by
                    intro _
                    exact k10t5_cover36
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover37
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k10t5_cover38
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover39
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover40
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
                    exact k10t5_cover43
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover44
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover45
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover46
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
            exact k10t5_cover47
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
            exact k10t5_cover48
        · intro q
          exact Fin.elim0 q

private theorem k10t5_cover3 : ∀ P ∈ pathPatterns 4 5 [], HasCheckedCertificate 10 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k10t5_seq4


private theorem k10t5_cover50 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 10 5 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover51 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 10 5 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p25, Certificates.k10t5p25_check⟩

private theorem k10t5_cover52 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 10 5 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p26, Certificates.k10t5p26_check⟩

private theorem k10t5_cover53 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 10 5 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p27, Certificates.k10t5p27_check⟩

private theorem k10t5_cover54 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 10 5 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover55 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 10 5 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p28, Certificates.k10t5p28_check⟩

private theorem k10t5_cover56 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 10 5 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover57 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 10 5 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover49 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 10 5 ([[1]] ++ P) := by
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
                exact k10t5_cover50
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t5_cover51
              · exact by
                  intro _
                  exact k10t5_cover52
              · exact by
                  intro _
                  exact k10t5_cover53
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover54
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k10t5_cover55
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover56
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover57
            · intro q
              exact Fin.elim0 q

private theorem k10t5_cover59 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 10 5 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p29, Certificates.k10t5p29_check⟩

private theorem k10t5_cover60 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 10 5 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p30, Certificates.k10t5p30_check⟩

private theorem k10t5_cover58 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 10 5 ([[1, 1]] ++ P) := by
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
            exact k10t5_cover59
        · exact by
            intro _
            exact k10t5_cover60

private theorem k10t5_cover61 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 10 5 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover62 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 10 5 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p31, Certificates.k10t5p31_check⟩

private theorem k10t5_cover63 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 10 5 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p32, Certificates.k10t5p32_check⟩

private theorem k10t5_cover64 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 10 5 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover65 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 10 5 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p33, Certificates.k10t5p33_check⟩

private theorem k10t5_cover66 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 10 5 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover68 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 5 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t5p34, Certificates.k10t5p34_check⟩

private theorem k10t5_cover67 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 10 5 ([[1, 2]] ++ P) := by
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
        · exact by
            intro _
            exact k10t5_cover68

private theorem k10t5_cover69 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 10 5 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover70 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 10 5 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover71 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 10 5 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k10t5_cover72 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 10 5 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover73 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 10 5 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t5_cover75 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 10 5 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover76 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 10 5 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover74 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 10 5 ([[2]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover75
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t5_cover76
            · intro q
              exact Fin.elim0 q

private theorem k10t5_cover77 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 10 5 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t5_cover78 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 10 5 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k10t5_cover79 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 10 5 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t5_cover80 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 10 5 ([[3]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k10t5_cover81 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 10 5 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k10t5_cover82 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 10 5 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t5_seq2 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 10 5 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k10t5_cover3
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover49
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover58
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover61
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k10t5_cover62
                      · exact by
                          intro _
                          exact k10t5_cover63
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover64
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k10t5_cover65
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover66
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover67
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover69
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover70
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover71
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover72
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover73
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover74
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k10t5_cover77
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover78
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k10t5_cover79
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k10t5_cover80
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
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
            exact k10t5_cover81
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
            exact k10t5_cover82
        · intro q
          exact Fin.elim0 q

private theorem k10t5_cover1 : ∀ P ∈ pathPatterns 5 5 [], HasCheckedCertificate 10 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k10t5_seq2


theorem coverage_k10_t5 :
    ∀ P ∈ pathPatterns 5 5, HasCheckedCertificate 10 5 P :=
  k10t5_cover1

private theorem k10t6_cover7 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 10 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p0, Certificates.k10t6p0_check⟩

private theorem k10t6_cover6 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 10 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k10t6_cover7

private theorem k10t6_cover8 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 10 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p1, Certificates.k10t6p1_check⟩

private theorem k10t6_cover9 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 10 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p2, Certificates.k10t6p2_check⟩

private theorem k10t6_cover10 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 10 6 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p3, Certificates.k10t6p3_check⟩

private theorem k10t6_cover11 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 10 6 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p4, Certificates.k10t6p4_check⟩

private theorem k10t6_cover5 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 10 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t6_cover6
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k10t6_cover8
        · exact by
            intro _
            exact k10t6_cover9
        · exact by
            intro _
            exact k10t6_cover10
        · exact by
            intro _
            exact k10t6_cover11

private theorem k10t6_cover12 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 10 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover13 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 10 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p5, Certificates.k10t6p5_check⟩

private theorem k10t6_cover14 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 10 6 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p6, Certificates.k10t6p6_check⟩

private theorem k10t6_cover15 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 10 6 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p7, Certificates.k10t6p7_check⟩

private theorem k10t6_cover16 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 10 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover17 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 10 6 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p8, Certificates.k10t6p8_check⟩

private theorem k10t6_cover18 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 10 6 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover19 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 10 6 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover4 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 10 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t6_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover12
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t6_cover13
              · exact by
                  intro _
                  exact k10t6_cover14
              · exact by
                  intro _
                  exact k10t6_cover15
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover16
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k10t6_cover17
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover18
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover19
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover21 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 10 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p9, Certificates.k10t6p9_check⟩

private theorem k10t6_cover22 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 10 6 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p10, Certificates.k10t6p10_check⟩

private theorem k10t6_cover23 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 10 6 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p11, Certificates.k10t6p11_check⟩

private theorem k10t6_cover20 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 10 6 ([[], [], [1]] ++ P) := by
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
            exact k10t6_cover21
        · exact by
            intro _
            exact k10t6_cover22
        · exact by
            intro _
            exact k10t6_cover23

private theorem k10t6_cover24 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 10 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover25 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 10 6 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p12, Certificates.k10t6p12_check⟩

private theorem k10t6_cover26 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 10 6 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p13, Certificates.k10t6p13_check⟩

private theorem k10t6_cover27 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 10 6 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover28 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 10 6 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p14, Certificates.k10t6p14_check⟩

private theorem k10t6_cover29 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 10 6 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover31 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 6 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p15, Certificates.k10t6p15_check⟩

private theorem k10t6_cover30 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 10 6 ([[], [], [2]] ++ P) := by
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
            exact k10t6_cover31

private theorem k10t6_cover32 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 10 6 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover33 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 10 6 ([[], [], [3]] ++ P) := by
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

private theorem k10t6_cover34 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 10 6 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover3 : ∀ P ∈ pathPatterns 4 4 [], HasCheckedCertificate 10 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t6_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover20
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover24
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k10t6_cover25
                    · exact by
                        intro _
                        exact k10t6_cover26
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover27
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k10t6_cover28
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover29
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover30
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
                      exact k10t6_cover32
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover33
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
                exact k10t6_cover34
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover36 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 10 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover37 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 10 6 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p16, Certificates.k10t6p16_check⟩

private theorem k10t6_cover38 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 10 6 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p17, Certificates.k10t6p17_check⟩

private theorem k10t6_cover39 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 10 6 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover40 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 10 6 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover35 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 10 6 ([[], [1]] ++ P) := by
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
                exact k10t6_cover36
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t6_cover37
              · exact by
                  intro _
                  exact k10t6_cover38
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover39
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover40
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover42 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 6 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p18, Certificates.k10t6p18_check⟩

private theorem k10t6_cover41 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 10 6 ([[], [1, 1]] ++ P) := by
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
            exact k10t6_cover42

private theorem k10t6_cover43 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 10 6 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover44 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 10 6 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p19, Certificates.k10t6p19_check⟩

private theorem k10t6_cover45 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 10 6 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover46 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 10 6 ([[], [1, 2]] ++ P) := by
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

private theorem k10t6_cover47 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 10 6 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover48 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 10 6 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover50 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 10 6 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover49 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 10 6 ([[], [2]] ++ P) := by
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
                exact k10t6_cover50
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover51 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 10 6 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover52 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 10 6 ([[], [3]] ++ P) := by
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

private theorem k10t6_cover53 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 10 6 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover2 : ∀ P ∈ pathPatterns 5 4 [], HasCheckedCertificate 10 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t6_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover35
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover41
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover43
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k10t6_cover44
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover45
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover46
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover47
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover48
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover49
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
                      exact k10t6_cover51
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover52
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
                exact k10t6_cover53
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover56 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 10 6 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p20, Certificates.k10t6p20_check⟩

private theorem k10t6_cover57 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 6 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p21, Certificates.k10t6p21_check⟩

private theorem k10t6_cover55 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 10 6 ([[1], [1]] ++ P) := by
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
            exact k10t6_cover56
        · exact by
            intro _
            exact k10t6_cover57

private theorem k10t6_cover58 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 10 6 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover59 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 10 6 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p22, Certificates.k10t6p22_check⟩

private theorem k10t6_cover60 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 10 6 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover61 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 10 6 ([[1], [2]] ++ P) := by
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

private theorem k10t6_cover62 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 10 6 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover54 : ∀ P ∈ pathPatterns 4 3 [1], HasCheckedCertificate 10 6 ([[1]] ++ P) := by
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
                exact k10t6_cover55
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover58
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k10t6_cover59
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover60
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover61
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover62
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover64 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 10 6 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t6p23, Certificates.k10t6p23_check⟩

private theorem k10t6_cover65 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 10 6 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover63 : ∀ P ∈ pathPatterns 3 2 [1, 1], HasCheckedCertificate 10 6 ([[1, 1]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro _
                  exact k10t6_cover64
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover65
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover66 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1], HasCheckedCertificate 10 6 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k10t6_cover67 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1], HasCheckedCertificate 10 6 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t6_cover68 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2], HasCheckedCertificate 10 6 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover69 : ∀ P ∈ pathPatterns 3 1 [1, 2], HasCheckedCertificate 10 6 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover70 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1], HasCheckedCertificate 10 6 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover71 : ∀ P ∈ pathPatterns 3 0 [1, 3], HasCheckedCertificate 10 6 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover73 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 10 6 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover72 : ∀ P ∈ pathPatterns 4 2 [2], HasCheckedCertificate 10 6 ([[2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover73
            · intro q
              exact Fin.elim0 q

private theorem k10t6_cover74 : ∀ P ∈ pathPatterns 3 0 [2, 2], HasCheckedCertificate 10 6 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover75 : ∀ P ∈ pathPatterns 4 1 [3], HasCheckedCertificate 10 6 ([[3]] ++ P) := by
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

private theorem k10t6_cover76 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 10 6 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t6_cover1 : ∀ P ∈ pathPatterns 6 4 [], HasCheckedCertificate 10 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t6_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover54
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover63
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover66
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k10t6_cover67
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover68
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover69
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t6_cover70
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t6_cover71
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover72
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
                      exact k10t6_cover74
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t6_cover75
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
                exact k10t6_cover76
            · intro q
              exact Fin.elim0 q

theorem coverage_k10_t6 :
    ∀ P ∈ pathPatterns 6 4, HasCheckedCertificate 10 6 P :=
  k10t6_cover1

private theorem k10t7_cover8 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 10 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p0, Certificates.k10t7p0_check⟩

private theorem k10t7_cover7 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 10 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k10t7_cover8

private theorem k10t7_cover9 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 10 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p1, Certificates.k10t7p1_check⟩

private theorem k10t7_cover10 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 10 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p2, Certificates.k10t7p2_check⟩

private theorem k10t7_cover11 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 10 7 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p3, Certificates.k10t7p3_check⟩

private theorem k10t7_cover6 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 10 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k10t7_cover9
        · exact by
            intro _
            exact k10t7_cover10
        · exact by
            intro _
            exact k10t7_cover11

private theorem k10t7_cover12 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 10 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover13 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 10 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p4, Certificates.k10t7p4_check⟩

private theorem k10t7_cover14 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 10 7 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p5, Certificates.k10t7p5_check⟩

private theorem k10t7_cover15 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 10 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover16 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 10 7 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover5 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 10 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover12
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t7_cover13
              · exact by
                  intro _
                  exact k10t7_cover14
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover15
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover16
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover18 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 10 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p6, Certificates.k10t7p6_check⟩

private theorem k10t7_cover19 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 7 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p7, Certificates.k10t7p7_check⟩

private theorem k10t7_cover17 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 10 7 ([[], [], [], [1]] ++ P) := by
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
            exact k10t7_cover18
        · exact by
            intro _
            exact k10t7_cover19

private theorem k10t7_cover20 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 10 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover21 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 10 7 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p8, Certificates.k10t7p8_check⟩

private theorem k10t7_cover22 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 10 7 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover23 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 10 7 ([[], [], [], [2]] ++ P) := by
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

private theorem k10t7_cover24 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 10 7 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover4 : ∀ P ∈ pathPatterns 4 3 [], HasCheckedCertificate 10 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover17
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover20
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k10t7_cover21
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover22
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover23
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
                exact k10t7_cover24
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover26 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 10 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover27 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 10 7 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p9, Certificates.k10t7p9_check⟩

private theorem k10t7_cover28 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 10 7 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover25 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 10 7 ([[], [], [1]] ++ P) := by
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
                exact k10t7_cover26
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t7_cover27
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover28
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover29 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 10 7 ([[], [], [1, 1]] ++ P) := by
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

private theorem k10t7_cover30 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 10 7 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover31 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 10 7 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover32 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 10 7 ([[], [], [2]] ++ P) := by
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

private theorem k10t7_cover33 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 10 7 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover3 : ∀ P ∈ pathPatterns 5 3 [], HasCheckedCertificate 10 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover25
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover29
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t7_cover30
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover31
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover32
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
                exact k10t7_cover33
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover36 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 10 7 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t7p10, Certificates.k10t7p10_check⟩

private theorem k10t7_cover35 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 10 7 ([[], [1], [1]] ++ P) := by
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
            exact k10t7_cover36

private theorem k10t7_cover37 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 10 7 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover38 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 10 7 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover34 : ∀ P ∈ pathPatterns 4 2 [1], HasCheckedCertificate 10 7 ([[], [1]] ++ P) := by
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
                exact k10t7_cover35
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover37
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover38
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover39 : ∀ P ∈ pathPatterns 3 1 [1, 1], HasCheckedCertificate 10 7 ([[], [1, 1]] ++ P) := by
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

private theorem k10t7_cover40 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1], HasCheckedCertificate 10 7 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover41 : ∀ P ∈ pathPatterns 3 0 [1, 2], HasCheckedCertificate 10 7 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover42 : ∀ P ∈ pathPatterns 4 1 [2], HasCheckedCertificate 10 7 ([[], [2]] ++ P) := by
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

private theorem k10t7_cover43 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 10 7 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover2 : ∀ P ∈ pathPatterns 6 3 [], HasCheckedCertificate 10 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover34
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover39
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t7_cover40
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover41
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover42
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
                exact k10t7_cover43
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover46 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 10 7 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t7_cover45 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 10 7 ([[1], [1]] ++ P) := by
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
                exact k10t7_cover46
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover47 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 10 7 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover48 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 10 7 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover44 : ∀ P ∈ pathPatterns 5 2 [1], HasCheckedCertificate 10 7 ([[1]] ++ P) := by
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
                exact k10t7_cover45
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover47
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover48
            · intro q
              exact Fin.elim0 q

private theorem k10t7_cover49 : ∀ P ∈ pathPatterns 4 1 [1, 1], HasCheckedCertificate 10 7 ([[1, 1]] ++ P) := by
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

private theorem k10t7_cover50 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1], HasCheckedCertificate 10 7 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover51 : ∀ P ∈ pathPatterns 4 0 [1, 2], HasCheckedCertificate 10 7 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover52 : ∀ P ∈ pathPatterns 5 1 [2], HasCheckedCertificate 10 7 ([[2]] ++ P) := by
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

private theorem k10t7_cover53 : ∀ P ∈ pathPatterns 5 0 [3], HasCheckedCertificate 10 7 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t7_cover1 : ∀ P ∈ pathPatterns 7 3 [], HasCheckedCertificate 10 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t7_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover44
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover49
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k10t7_cover50
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t7_cover51
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t7_cover52
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
                exact k10t7_cover53
            · intro q
              exact Fin.elim0 q

theorem coverage_k10_t7 :
    ∀ P ∈ pathPatterns 7 3, HasCheckedCertificate 10 7 P :=
  k10t7_cover1

private theorem k10t8_cover9 : ∀ P ∈ pathPatterns 0 2 [], HasCheckedCertificate 10 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t8p0, Certificates.k10t8p0_check⟩

private theorem k10t8_cover8 : ∀ P ∈ pathPatterns 1 2 [], HasCheckedCertificate 10 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k10t8_cover9

private theorem k10t8_cover10 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 10 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t8p1, Certificates.k10t8p1_check⟩

private theorem k10t8_cover11 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 10 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t8p2, Certificates.k10t8p2_check⟩

private theorem k10t8_cover7 : ∀ P ∈ pathPatterns 2 2 [], HasCheckedCertificate 10 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover8
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k10t8_cover10
        · exact by
            intro _
            exact k10t8_cover11

private theorem k10t8_cover12 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 10 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t8_cover13 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 10 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t8p3, Certificates.k10t8p3_check⟩

private theorem k10t8_cover14 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 10 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k10t8_cover6 : ∀ P ∈ pathPatterns 3 2 [], HasCheckedCertificate 10 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover7
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover12
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k10t8_cover13
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover14
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover16 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 10 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k10t8p4, Certificates.k10t8p4_check⟩

private theorem k10t8_cover15 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 10 8 ([[], [], [], [], [1]] ++ P) := by
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
            exact k10t8_cover16

private theorem k10t8_cover17 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 10 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k10t8_cover18 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 10 8 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover5 : ∀ P ∈ pathPatterns 4 2 [], HasCheckedCertificate 10 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover15
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t8_cover17
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover18
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover20 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 10 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k10t8_cover19 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 10 8 ([[], [], [], [1]] ++ P) := by
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
                exact k10t8_cover20
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover21 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 10 8 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover22 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 10 8 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover4 : ∀ P ∈ pathPatterns 5 2 [], HasCheckedCertificate 10 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover19
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t8_cover21
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover22
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover24 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 10 8 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover23 : ∀ P ∈ pathPatterns 4 1 [1], HasCheckedCertificate 10 8 ([[], [], [1]] ++ P) := by
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
                exact k10t8_cover24
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover25 : ∀ P ∈ pathPatterns 3 0 [1, 1], HasCheckedCertificate 10 8 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover26 : ∀ P ∈ pathPatterns 4 0 [2], HasCheckedCertificate 10 8 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover3 : ∀ P ∈ pathPatterns 6 2 [], HasCheckedCertificate 10 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover23
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t8_cover25
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover26
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover28 : ∀ P ∈ pathPatterns 3 0 [1], HasCheckedCertificate 10 8 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover27 : ∀ P ∈ pathPatterns 5 1 [1], HasCheckedCertificate 10 8 ([[], [1]] ++ P) := by
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
                exact k10t8_cover28
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover29 : ∀ P ∈ pathPatterns 4 0 [1, 1], HasCheckedCertificate 10 8 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover30 : ∀ P ∈ pathPatterns 5 0 [2], HasCheckedCertificate 10 8 ([[], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover2 : ∀ P ∈ pathPatterns 7 2 [], HasCheckedCertificate 10 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover27
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t8_cover29
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover30
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover32 : ∀ P ∈ pathPatterns 4 0 [1], HasCheckedCertificate 10 8 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover31 : ∀ P ∈ pathPatterns 6 1 [1], HasCheckedCertificate 10 8 ([[1]] ++ P) := by
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
                exact k10t8_cover32
            · intro q
              exact Fin.elim0 q

private theorem k10t8_cover33 : ∀ P ∈ pathPatterns 5 0 [1, 1], HasCheckedCertificate 10 8 ([[1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover34 : ∀ P ∈ pathPatterns 6 0 [2], HasCheckedCertificate 10 8 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k10t8_cover1 : ∀ P ∈ pathPatterns 8 2 [], HasCheckedCertificate 10 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k10t8_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover31
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k10t8_cover33
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k10t8_cover34
            · intro q
              exact Fin.elim0 q

theorem coverage_k10_t8 :
    ∀ P ∈ pathPatterns 8 2, HasCheckedCertificate 10 8 P :=
  k10t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
