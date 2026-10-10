import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK12
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k12t6_cover10 : ∀ P ∈ pathPatterns 0 6 [], HasCheckedCertificate 12 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p0, Certificates.k12t6p0_check⟩

private theorem k12t6_cover9 : ∀ P ∈ pathPatterns 1 6 [], HasCheckedCertificate 12 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k12t6_cover10

private theorem k12t6_cover11 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 12 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p1, Certificates.k12t6p1_check⟩

private theorem k12t6_cover12 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 12 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p2, Certificates.k12t6p2_check⟩

private theorem k12t6_cover13 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 12 6 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p3, Certificates.k12t6p3_check⟩

private theorem k12t6_cover14 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 12 6 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p4, Certificates.k12t6p4_check⟩

private theorem k12t6_cover15 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 12 6 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p5, Certificates.k12t6p5_check⟩

private theorem k12t6_cover16 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 12 6 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p6, Certificates.k12t6p6_check⟩

private theorem k12t6_cover8 : ∀ P ∈ pathPatterns 2 6 [], HasCheckedCertificate 12 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t6_cover9
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k12t6_cover11
        · exact by
            intro _
            exact k12t6_cover12
        · exact by
            intro _
            exact k12t6_cover13
        · exact by
            intro _
            exact k12t6_cover14
        · exact by
            intro _
            exact k12t6_cover15
        · exact by
            intro _
            exact k12t6_cover16

private theorem k12t6_cover17 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 12 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover18 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 12 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p7, Certificates.k12t6p7_check⟩

private theorem k12t6_cover19 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 12 6 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p8, Certificates.k12t6p8_check⟩

private theorem k12t6_cover20 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 12 6 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p9, Certificates.k12t6p9_check⟩

private theorem k12t6_cover21 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 12 6 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p10, Certificates.k12t6p10_check⟩

private theorem k12t6_cover22 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 12 6 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p11, Certificates.k12t6p11_check⟩

private theorem k12t6_cover23 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 12 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover24 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 12 6 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p12, Certificates.k12t6p12_check⟩

private theorem k12t6_cover25 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 12 6 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p13, Certificates.k12t6p13_check⟩

private theorem k12t6_cover26 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 12 6 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p14, Certificates.k12t6p14_check⟩

private theorem k12t6_cover27 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 12 6 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover28 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 12 6 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p15, Certificates.k12t6p15_check⟩

private theorem k12t6_cover29 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 12 6 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover30 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 12 6 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover31 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 12 6 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover7 : ∀ P ∈ pathPatterns 3 6 [], HasCheckedCertificate 12 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t6_cover8
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover17
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t6_cover18
              · exact by
                  intro _
                  exact k12t6_cover19
              · exact by
                  intro _
                  exact k12t6_cover20
              · exact by
                  intro _
                  exact k12t6_cover21
              · exact by
                  intro _
                  exact k12t6_cover22
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover23
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t6_cover24
              · exact by
                  intro _
                  exact k12t6_cover25
              · exact by
                  intro _
                  exact k12t6_cover26
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover27
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · exact by
                  intro _
                  exact k12t6_cover28
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover29
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover30
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover31
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover33 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 12 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p16, Certificates.k12t6p16_check⟩

private theorem k12t6_cover34 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 12 6 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p17, Certificates.k12t6p17_check⟩

private theorem k12t6_cover35 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 12 6 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p18, Certificates.k12t6p18_check⟩

private theorem k12t6_cover36 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 12 6 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p19, Certificates.k12t6p19_check⟩

private theorem k12t6_cover37 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 12 6 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p20, Certificates.k12t6p20_check⟩

private theorem k12t6_cover32 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 12 6 ([[], [], [1]] ++ P) := by
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
            exact k12t6_cover33
        · exact by
            intro _
            exact k12t6_cover34
        · exact by
            intro _
            exact k12t6_cover35
        · exact by
            intro _
            exact k12t6_cover36
        · exact by
            intro _
            exact k12t6_cover37

private theorem k12t6_cover38 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 12 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover39 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 12 6 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p21, Certificates.k12t6p21_check⟩

private theorem k12t6_cover40 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 12 6 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p22, Certificates.k12t6p22_check⟩

private theorem k12t6_cover41 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 12 6 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p23, Certificates.k12t6p23_check⟩

private theorem k12t6_cover42 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 12 6 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p24, Certificates.k12t6p24_check⟩

private theorem k12t6_cover43 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 12 6 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover44 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 12 6 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p25, Certificates.k12t6p25_check⟩

private theorem k12t6_cover45 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 12 6 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p26, Certificates.k12t6p26_check⟩

private theorem k12t6_cover46 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 12 6 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p27, Certificates.k12t6p27_check⟩

private theorem k12t6_cover47 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 12 6 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover48 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 12 6 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p28, Certificates.k12t6p28_check⟩

private theorem k12t6_cover49 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 12 6 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p29, Certificates.k12t6p29_check⟩

private theorem k12t6_cover50 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 12 6 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover51 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 12 6 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p30, Certificates.k12t6p30_check⟩

private theorem k12t6_cover52 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 12 6 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover54 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 12 6 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p31, Certificates.k12t6p31_check⟩

private theorem k12t6_cover55 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 12 6 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p32, Certificates.k12t6p32_check⟩

private theorem k12t6_cover56 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 12 6 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p33, Certificates.k12t6p33_check⟩

private theorem k12t6_cover53 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 12 6 ([[], [], [2]] ++ P) := by
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
            exact k12t6_cover54
        · exact by
            intro _
            exact k12t6_cover55
        · exact by
            intro _
            exact k12t6_cover56

private theorem k12t6_cover57 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 12 6 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p34, Certificates.k12t6p34_check⟩

private theorem k12t6_cover58 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 12 6 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p35, Certificates.k12t6p35_check⟩

private theorem k12t6_cover59 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 12 6 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover60 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 12 6 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p36, Certificates.k12t6p36_check⟩

private theorem k12t6_cover61 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 12 6 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover62 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 12 6 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover64 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 6 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p37, Certificates.k12t6p37_check⟩

private theorem k12t6_cover63 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 12 6 ([[], [], [3]] ++ P) := by
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
        · exact by
            intro _
            exact k12t6_cover64

private theorem k12t6_cover65 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 12 6 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover66 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 12 6 ([[], [], [4]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)

private theorem k12t6_cover67 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 12 6 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover68 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 12 6 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq6 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 6 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t6_cover7
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover32
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover38
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover39
                · exact by
                    intro _
                    exact k12t6_cover40
                · exact by
                    intro _
                    exact k12t6_cover41
                · exact by
                    intro _
                    exact k12t6_cover42
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover43
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover44
                · exact by
                    intro _
                    exact k12t6_cover45
                · exact by
                    intro _
                    exact k12t6_cover46
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover47
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover48
                · exact by
                    intro _
                    exact k12t6_cover49
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover50
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover51
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover52
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover53
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
                    exact k12t6_cover57
                · exact by
                    intro _
                    exact k12t6_cover58
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover59
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k12t6_cover60
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover61
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover62
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover63
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover65
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover66
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover67
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover68
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover5 : ∀ P ∈ pathPatterns 4 6 [], HasCheckedCertificate 12 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t6_seq6


private theorem k12t6_cover71 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 12 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover72 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 12 6 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p38, Certificates.k12t6p38_check⟩

private theorem k12t6_cover73 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 12 6 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p39, Certificates.k12t6p39_check⟩

private theorem k12t6_cover74 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 12 6 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p40, Certificates.k12t6p40_check⟩

private theorem k12t6_cover75 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 12 6 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p41, Certificates.k12t6p41_check⟩

private theorem k12t6_cover76 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 12 6 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover77 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 12 6 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p42, Certificates.k12t6p42_check⟩

private theorem k12t6_cover78 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 12 6 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p43, Certificates.k12t6p43_check⟩

private theorem k12t6_cover79 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 12 6 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover80 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 12 6 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover81 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 12 6 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover70 : ∀ P ∈ pathPatterns 3 5 [1], HasCheckedCertificate 12 6 ([[], [1]] ++ P) := by
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
                exact k12t6_cover71
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t6_cover72
              · exact by
                  intro _
                  exact k12t6_cover73
              · exact by
                  intro _
                  exact k12t6_cover74
              · exact by
                  intro _
                  exact k12t6_cover75
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover76
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t6_cover77
              · exact by
                  intro _
                  exact k12t6_cover78
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover79
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover80
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover81
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover83 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 12 6 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p44, Certificates.k12t6p44_check⟩

private theorem k12t6_cover84 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 12 6 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p45, Certificates.k12t6p45_check⟩

private theorem k12t6_cover85 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 12 6 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p46, Certificates.k12t6p46_check⟩

private theorem k12t6_cover82 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 12 6 ([[], [1, 1]] ++ P) := by
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
            exact k12t6_cover83
        · exact by
            intro _
            exact k12t6_cover84
        · exact by
            intro _
            exact k12t6_cover85

private theorem k12t6_cover86 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 12 6 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover87 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 12 6 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p47, Certificates.k12t6p47_check⟩

private theorem k12t6_cover88 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 12 6 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p48, Certificates.k12t6p48_check⟩

private theorem k12t6_cover89 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 12 6 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p49, Certificates.k12t6p49_check⟩

private theorem k12t6_cover90 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 12 6 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover91 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 12 6 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p50, Certificates.k12t6p50_check⟩

private theorem k12t6_cover92 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 12 6 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p51, Certificates.k12t6p51_check⟩

private theorem k12t6_cover93 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 12 6 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover94 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 12 6 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p52, Certificates.k12t6p52_check⟩

private theorem k12t6_cover95 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 12 6 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover97 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 6 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p53, Certificates.k12t6p53_check⟩

private theorem k12t6_cover98 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 6 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p54, Certificates.k12t6p54_check⟩

private theorem k12t6_cover96 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 12 6 ([[], [1, 2]] ++ P) := by
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
            exact k12t6_cover97
        · exact by
            intro _
            exact k12t6_cover98

private theorem k12t6_cover99 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 12 6 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover100 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 12 6 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p55, Certificates.k12t6p55_check⟩

private theorem k12t6_cover101 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 12 6 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover102 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 12 6 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p56, Certificates.k12t6p56_check⟩

private theorem k12t6_cover103 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 12 6 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover105 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 6 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p57, Certificates.k12t6p57_check⟩

private theorem k12t6_cover104 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 12 6 ([[], [1, 3]] ++ P) := by
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
        · exact by
            intro _
            exact k12t6_cover105

private theorem k12t6_cover106 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 12 6 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover107 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 12 6 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover108 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 12 6 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover109 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 12 6 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover110 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 12 6 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq69 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 12 6 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t6_cover70
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover82
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover86
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover87
                · exact by
                    intro _
                    exact k12t6_cover88
                · exact by
                    intro _
                    exact k12t6_cover89
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover90
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover91
                · exact by
                    intro _
                    exact k12t6_cover92
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover93
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover94
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover95
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover96
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover99
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k12t6_cover100
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover101
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover102
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover103
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover104
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover106
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover107
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover108
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover109
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover110
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover112 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 12 6 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover113 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 12 6 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p58, Certificates.k12t6p58_check⟩

private theorem k12t6_cover114 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 12 6 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover115 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 12 6 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover111 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 12 6 ([[], [2]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover112
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t6_cover113
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover114
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover115
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover116 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 12 6 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p59, Certificates.k12t6p59_check⟩

private theorem k12t6_cover117 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 12 6 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover118 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 12 6 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover119 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 12 6 ([[], [2, 2]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k12t6_cover120 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 12 6 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover121 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 12 6 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover122 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 12 6 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover124 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 6 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover123 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 12 6 ([[], [3]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover124
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover125 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 12 6 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover126 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 12 6 ([[], [4]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover127 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 12 6 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover128 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 12 6 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq4 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 6 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t6_cover5
  · intro q
    fin_cases q
    · exact k12t6_seq69

    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover111
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
                          intro _
                          exact k12t6_cover116
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover117
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover118
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover119
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover120
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover121
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover122
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover123
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover125
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover126
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover127
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover128
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover3 : ∀ P ∈ pathPatterns 5 6 [], HasCheckedCertificate 12 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t6_seq4


private theorem k12t6_cover133 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 12 6 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p60, Certificates.k12t6p60_check⟩

private theorem k12t6_cover134 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 12 6 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p61, Certificates.k12t6p61_check⟩

private theorem k12t6_cover135 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 12 6 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p62, Certificates.k12t6p62_check⟩

private theorem k12t6_cover136 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 12 6 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p63, Certificates.k12t6p63_check⟩

private theorem k12t6_cover132 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 12 6 ([[1], [1]] ++ P) := by
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
            exact k12t6_cover133
        · exact by
            intro _
            exact k12t6_cover134
        · exact by
            intro _
            exact k12t6_cover135
        · exact by
            intro _
            exact k12t6_cover136

private theorem k12t6_cover137 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 12 6 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover138 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 12 6 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p64, Certificates.k12t6p64_check⟩

private theorem k12t6_cover139 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 12 6 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p65, Certificates.k12t6p65_check⟩

private theorem k12t6_cover140 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 12 6 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p66, Certificates.k12t6p66_check⟩

private theorem k12t6_cover141 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 12 6 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover142 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 12 6 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p67, Certificates.k12t6p67_check⟩

private theorem k12t6_cover143 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 12 6 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p68, Certificates.k12t6p68_check⟩

private theorem k12t6_cover144 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 12 6 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover145 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 12 6 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p69, Certificates.k12t6p69_check⟩

private theorem k12t6_cover146 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 12 6 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover148 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 6 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p70, Certificates.k12t6p70_check⟩

private theorem k12t6_cover149 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 6 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p71, Certificates.k12t6p71_check⟩

private theorem k12t6_cover147 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 12 6 ([[1], [2]] ++ P) := by
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
            exact k12t6_cover148
        · exact by
            intro _
            exact k12t6_cover149

private theorem k12t6_cover150 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 12 6 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p72, Certificates.k12t6p72_check⟩

private theorem k12t6_cover151 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 12 6 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover152 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 12 6 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover153 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 12 6 ([[1], [3]] ++ P) := by
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

private theorem k12t6_cover154 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 12 6 ([[1], [4]] ++ P) := by
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

private theorem k12t6_cover155 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 12 6 ([[1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq131 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 6 ([[1]] ++ (([] ++ tail) :: P))) :=
by
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
            exact k12t6_cover132
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover137
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover138
                · exact by
                    intro _
                    exact k12t6_cover139
                · exact by
                    intro _
                    exact k12t6_cover140
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover141
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover142
                · exact by
                    intro _
                    exact k12t6_cover143
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover144
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t6_cover145
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover146
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover147
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                · exact by
                    intro _
                    exact k12t6_cover150
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover151
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover152
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover153
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover154
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover155
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover130 : ∀ P ∈ pathPatterns 4 5 [1], HasCheckedCertificate 12 6 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t6_seq131


private theorem k12t6_cover157 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 12 6 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p73, Certificates.k12t6p73_check⟩

private theorem k12t6_cover158 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 12 6 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p74, Certificates.k12t6p74_check⟩

private theorem k12t6_cover159 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 12 6 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p75, Certificates.k12t6p75_check⟩

private theorem k12t6_cover160 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 12 6 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover161 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 12 6 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p76, Certificates.k12t6p76_check⟩

private theorem k12t6_cover162 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 12 6 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover163 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 12 6 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover156 : ∀ P ∈ pathPatterns 3 4 [1, 1], HasCheckedCertificate 12 6 ([[1, 1]] ++ P) := by
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
                  exact k12t6_cover157
              · exact by
                  intro _
                  exact k12t6_cover158
              · exact by
                  intro _
                  exact k12t6_cover159
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover160
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t6_cover161
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover162
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover163
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover165 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 6 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p77, Certificates.k12t6p77_check⟩

private theorem k12t6_cover166 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 6 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p78, Certificates.k12t6p78_check⟩

private theorem k12t6_cover164 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1], HasCheckedCertificate 12 6 ([[1, 1, 1]] ++ P) := by
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
        · exact by
            intro _
            exact k12t6_cover165
        · exact by
            intro _
            exact k12t6_cover166

private theorem k12t6_cover167 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1], HasCheckedCertificate 12 6 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover168 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1], HasCheckedCertificate 12 6 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p79, Certificates.k12t6p79_check⟩

private theorem k12t6_cover169 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2], HasCheckedCertificate 12 6 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p80, Certificates.k12t6p80_check⟩

private theorem k12t6_cover170 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2], HasCheckedCertificate 12 6 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover171 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1], HasCheckedCertificate 12 6 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p81, Certificates.k12t6p81_check⟩

private theorem k12t6_cover172 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3], HasCheckedCertificate 12 6 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover174 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 6 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p82, Certificates.k12t6p82_check⟩

private theorem k12t6_cover173 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2], HasCheckedCertificate 12 6 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k12t6_cover174

private theorem k12t6_cover175 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 1], HasCheckedCertificate 12 6 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover176 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 1], HasCheckedCertificate 12 6 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p83, Certificates.k12t6p83_check⟩

private theorem k12t6_cover177 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2], HasCheckedCertificate 12 6 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover178 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3], HasCheckedCertificate 12 6 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover179 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 1], HasCheckedCertificate 12 6 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover180 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4], HasCheckedCertificate 12 6 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover182 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 12 6 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p84, Certificates.k12t6p84_check⟩

private theorem k12t6_cover183 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 12 6 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover184 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 6 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover181 : ∀ P ∈ pathPatterns 3 3 [1, 2], HasCheckedCertificate 12 6 ([[1, 2]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
              · exact by
                  intro _
                  exact k12t6_cover182
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover183
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover184
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover186 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 6 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p85, Certificates.k12t6p85_check⟩

private theorem k12t6_cover185 : ∀ P ∈ pathPatterns 2 2 [1, 2, 1], HasCheckedCertificate 12 6 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
        · exact by
            intro _
            exact k12t6_cover186

private theorem k12t6_cover187 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 2], HasCheckedCertificate 12 6 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover188 : ∀ P ∈ pathPatterns 2 1 [1, 2, 2], HasCheckedCertificate 12 6 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover189 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 1], HasCheckedCertificate 12 6 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover190 : ∀ P ∈ pathPatterns 2 0 [1, 2, 3], HasCheckedCertificate 12 6 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover192 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 6 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover191 : ∀ P ∈ pathPatterns 3 2 [1, 3], HasCheckedCertificate 12 6 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover192
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover193 : ∀ P ∈ pathPatterns 2 1 [1, 3, 1], HasCheckedCertificate 12 6 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover194 : ∀ P ∈ pathPatterns 2 0 [1, 3, 2], HasCheckedCertificate 12 6 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover195 : ∀ P ∈ pathPatterns 3 1 [1, 4], HasCheckedCertificate 12 6 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover196 : ∀ P ∈ pathPatterns 2 0 [1, 4, 1], HasCheckedCertificate 12 6 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover197 : ∀ P ∈ pathPatterns 3 0 [1, 5], HasCheckedCertificate 12 6 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq129 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 12 6 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t6_cover130
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover156
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover164
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover167
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k12t6_cover168
                      · exact by
                          intro _
                          exact k12t6_cover169
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover170
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k12t6_cover171
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover172
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover173
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover175
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k12t6_cover176
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover177
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover178
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover179
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover180
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover181
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover185
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover187
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover188
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover189
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover190
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover191
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover193
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover194
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover195
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover196
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover197
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover200 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 6 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t6p86, Certificates.k12t6p86_check⟩

private theorem k12t6_cover199 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 12 6 ([[2], [2]] ++ P) := by
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
            exact k12t6_cover200

private theorem k12t6_cover201 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 12 6 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover202 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 12 6 ([[2], [3]] ++ P) := by
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

private theorem k12t6_cover203 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 12 6 ([[2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover198 : ∀ P ∈ pathPatterns 4 4 [2], HasCheckedCertificate 12 6 ([[2]] ++ P) := by
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
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover199
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t6_cover201
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover202
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover203
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover204 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 2], HasCheckedCertificate 12 6 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t6_cover205 : ∀ P ∈ pathPatterns 2 1 [2, 1, 2], HasCheckedCertificate 12 6 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k12t6_cover206 : ∀ P ∈ pathPatterns 2 0 [2, 1, 3], HasCheckedCertificate 12 6 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover207 : ∀ P ∈ pathPatterns 3 2 [2, 2], HasCheckedCertificate 12 6 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover208 : ∀ P ∈ pathPatterns 2 0 [2, 2, 2], HasCheckedCertificate 12 6 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover209 : ∀ P ∈ pathPatterns 3 1 [2, 3], HasCheckedCertificate 12 6 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover210 : ∀ P ∈ pathPatterns 3 0 [2, 4], HasCheckedCertificate 12 6 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover212 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 12 6 ([[3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover211 : ∀ P ∈ pathPatterns 4 3 [3], HasCheckedCertificate 12 6 ([[3]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t6_cover212
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover213 : ∀ P ∈ pathPatterns 3 0 [3, 3], HasCheckedCertificate 12 6 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_cover214 : ∀ P ∈ pathPatterns 4 2 [4], HasCheckedCertificate 12 6 ([[4]] ++ P) := by
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
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover215 : ∀ P ∈ pathPatterns 4 1 [5], HasCheckedCertificate 12 6 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t6_cover216 : ∀ P ∈ pathPatterns 4 0 [6], HasCheckedCertificate 12 6 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t6_seq2 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 6 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t6_cover3
  · intro q
    fin_cases q
    · exact k12t6_seq129

    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover198
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
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                          · intro q
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t6_cover204
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover205
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover206
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover207
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1] ∧ LexLE [2, 2, 1, 1] [1, 1, 2, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t6_cover208
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover209
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover210
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover211
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
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1] ∧ LexLE [3, 1, 1, 1] [1, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t6_cover213
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover214
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover215
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t6_cover216
        · intro q
          exact Fin.elim0 q

private theorem k12t6_cover1 : ∀ P ∈ pathPatterns 6 6 [], HasCheckedCertificate 12 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t6_seq2


theorem coverage_k12_t6 :
    ∀ P ∈ pathPatterns 6 6, HasCheckedCertificate 12 6 P :=
  k12t6_cover1

private theorem k12t7_cover12 : ∀ P ∈ pathPatterns 0 5 [], HasCheckedCertificate 12 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p0, Certificates.k12t7p0_check⟩

private theorem k12t7_cover11 : ∀ P ∈ pathPatterns 1 5 [], HasCheckedCertificate 12 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k12t7_cover12

private theorem k12t7_cover13 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 12 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p1, Certificates.k12t7p1_check⟩

private theorem k12t7_cover14 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 12 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p2, Certificates.k12t7p2_check⟩

private theorem k12t7_cover15 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 12 7 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p3, Certificates.k12t7p3_check⟩

private theorem k12t7_cover16 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 12 7 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p4, Certificates.k12t7p4_check⟩

private theorem k12t7_cover17 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 12 7 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p5, Certificates.k12t7p5_check⟩

private theorem k12t7_cover10 : ∀ P ∈ pathPatterns 2 5 [], HasCheckedCertificate 12 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t7_cover11
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k12t7_cover13
        · exact by
            intro _
            exact k12t7_cover14
        · exact by
            intro _
            exact k12t7_cover15
        · exact by
            intro _
            exact k12t7_cover16
        · exact by
            intro _
            exact k12t7_cover17

private theorem k12t7_cover18 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 12 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover19 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 12 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p6, Certificates.k12t7p6_check⟩

private theorem k12t7_cover20 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 12 7 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p7, Certificates.k12t7p7_check⟩

private theorem k12t7_cover21 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 12 7 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p8, Certificates.k12t7p8_check⟩

private theorem k12t7_cover22 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 12 7 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p9, Certificates.k12t7p9_check⟩

private theorem k12t7_cover23 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 12 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover24 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 12 7 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p10, Certificates.k12t7p10_check⟩

private theorem k12t7_cover25 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 12 7 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p11, Certificates.k12t7p11_check⟩

private theorem k12t7_cover26 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 12 7 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover27 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 12 7 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover28 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 12 7 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover9 : ∀ P ∈ pathPatterns 3 5 [], HasCheckedCertificate 12 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t7_cover10
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover18
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t7_cover19
              · exact by
                  intro _
                  exact k12t7_cover20
              · exact by
                  intro _
                  exact k12t7_cover21
              · exact by
                  intro _
                  exact k12t7_cover22
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover23
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t7_cover24
              · exact by
                  intro _
                  exact k12t7_cover25
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover26
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
                exact k12t7_cover27
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover28
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover30 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 12 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p12, Certificates.k12t7p12_check⟩

private theorem k12t7_cover31 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 12 7 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p13, Certificates.k12t7p13_check⟩

private theorem k12t7_cover32 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 12 7 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p14, Certificates.k12t7p14_check⟩

private theorem k12t7_cover33 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 12 7 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p15, Certificates.k12t7p15_check⟩

private theorem k12t7_cover29 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 12 7 ([[], [], [], [1]] ++ P) := by
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
            exact k12t7_cover30
        · exact by
            intro _
            exact k12t7_cover31
        · exact by
            intro _
            exact k12t7_cover32
        · exact by
            intro _
            exact k12t7_cover33

private theorem k12t7_cover34 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 12 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover35 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 12 7 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p16, Certificates.k12t7p16_check⟩

private theorem k12t7_cover36 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 12 7 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p17, Certificates.k12t7p17_check⟩

private theorem k12t7_cover37 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 12 7 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p18, Certificates.k12t7p18_check⟩

private theorem k12t7_cover38 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 12 7 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover39 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 12 7 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p19, Certificates.k12t7p19_check⟩

private theorem k12t7_cover40 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 12 7 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p20, Certificates.k12t7p20_check⟩

private theorem k12t7_cover41 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 12 7 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover42 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 12 7 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p21, Certificates.k12t7p21_check⟩

private theorem k12t7_cover43 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 12 7 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover45 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 7 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p22, Certificates.k12t7p22_check⟩

private theorem k12t7_cover46 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 7 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p23, Certificates.k12t7p23_check⟩

private theorem k12t7_cover44 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 12 7 ([[], [], [], [2]] ++ P) := by
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
            exact k12t7_cover45
        · exact by
            intro _
            exact k12t7_cover46

private theorem k12t7_cover47 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 12 7 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p24, Certificates.k12t7p24_check⟩

private theorem k12t7_cover48 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 12 7 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover49 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 12 7 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover50 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 12 7 ([[], [], [], [3]] ++ P) := by
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

private theorem k12t7_cover51 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 12 7 ([[], [], [], [4]] ++ P) := by
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

private theorem k12t7_cover52 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 12 7 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_seq8 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 7 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t7_cover9
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover29
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover34
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t7_cover35
                · exact by
                    intro _
                    exact k12t7_cover36
                · exact by
                    intro _
                    exact k12t7_cover37
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover38
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t7_cover39
                · exact by
                    intro _
                    exact k12t7_cover40
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover41
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k12t7_cover42
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover43
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover44
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
                    exact k12t7_cover47
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover48
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover49
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover50
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
            exact k12t7_cover51
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
            exact k12t7_cover52
        · intro q
          exact Fin.elim0 q

private theorem k12t7_cover7 : ∀ P ∈ pathPatterns 4 5 [], HasCheckedCertificate 12 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t7_seq8


private theorem k12t7_cover54 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 12 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover55 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 12 7 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p25, Certificates.k12t7p25_check⟩

private theorem k12t7_cover56 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 12 7 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p26, Certificates.k12t7p26_check⟩

private theorem k12t7_cover57 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 12 7 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p27, Certificates.k12t7p27_check⟩

private theorem k12t7_cover58 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 12 7 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover59 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 12 7 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p28, Certificates.k12t7p28_check⟩

private theorem k12t7_cover60 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 12 7 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover61 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 12 7 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover53 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 12 7 ([[], [], [1]] ++ P) := by
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
                exact k12t7_cover54
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t7_cover55
              · exact by
                  intro _
                  exact k12t7_cover56
              · exact by
                  intro _
                  exact k12t7_cover57
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover58
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t7_cover59
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover60
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover61
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover63 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 7 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p29, Certificates.k12t7p29_check⟩

private theorem k12t7_cover64 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 7 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p30, Certificates.k12t7p30_check⟩

private theorem k12t7_cover62 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 12 7 ([[], [], [1, 1]] ++ P) := by
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
            exact k12t7_cover63
        · exact by
            intro _
            exact k12t7_cover64

private theorem k12t7_cover65 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 12 7 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover66 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 12 7 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p31, Certificates.k12t7p31_check⟩

private theorem k12t7_cover67 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 12 7 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p32, Certificates.k12t7p32_check⟩

private theorem k12t7_cover68 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 12 7 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover69 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 12 7 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p33, Certificates.k12t7p33_check⟩

private theorem k12t7_cover70 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 12 7 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover72 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 7 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p34, Certificates.k12t7p34_check⟩

private theorem k12t7_cover71 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 12 7 ([[], [], [1, 2]] ++ P) := by
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
            exact k12t7_cover72

private theorem k12t7_cover73 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 12 7 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover74 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 12 7 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover75 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 12 7 ([[], [], [1, 3]] ++ P) := by
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

private theorem k12t7_cover76 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 12 7 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover77 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 12 7 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover79 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 12 7 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover80 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 7 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover78 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 12 7 ([[], [], [2]] ++ P) := by
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
                exact k12t7_cover79
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover80
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover81 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 12 7 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover82 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 12 7 ([[], [], [2, 2]] ++ P) := by
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

private theorem k12t7_cover83 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 12 7 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover84 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 12 7 ([[], [], [3]] ++ P) := by
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

private theorem k12t7_cover85 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 12 7 ([[], [], [4]] ++ P) := by
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

private theorem k12t7_cover86 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 12 7 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_seq6 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 7 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t7_cover7
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover53
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover62
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover65
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k12t7_cover66
                      · exact by
                          intro _
                          exact k12t7_cover67
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover68
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k12t7_cover69
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover70
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover71
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover73
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover74
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover75
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover76
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover77
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover78
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
                        exact k12t7_cover81
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover82
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
                  exact k12t7_cover83
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover84
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
            exact k12t7_cover85
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
            exact k12t7_cover86
        · intro q
          exact Fin.elim0 q

private theorem k12t7_cover5 : ∀ P ∈ pathPatterns 5 5 [], HasCheckedCertificate 12 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t7_seq6


private theorem k12t7_cover89 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 12 7 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p35, Certificates.k12t7p35_check⟩

private theorem k12t7_cover90 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 7 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p36, Certificates.k12t7p36_check⟩

private theorem k12t7_cover91 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 7 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p37, Certificates.k12t7p37_check⟩

private theorem k12t7_cover88 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 12 7 ([[], [1], [1]] ++ P) := by
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
            exact k12t7_cover89
        · exact by
            intro _
            exact k12t7_cover90
        · exact by
            intro _
            exact k12t7_cover91

private theorem k12t7_cover92 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 12 7 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover93 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 12 7 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p38, Certificates.k12t7p38_check⟩

private theorem k12t7_cover94 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 12 7 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p39, Certificates.k12t7p39_check⟩

private theorem k12t7_cover95 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 12 7 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover96 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 12 7 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p40, Certificates.k12t7p40_check⟩

private theorem k12t7_cover97 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 12 7 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover99 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 7 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p41, Certificates.k12t7p41_check⟩

private theorem k12t7_cover98 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 12 7 ([[], [1], [2]] ++ P) := by
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
            exact k12t7_cover99

private theorem k12t7_cover100 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 12 7 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover101 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 12 7 ([[], [1], [3]] ++ P) := by
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

private theorem k12t7_cover102 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 12 7 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover87 : ∀ P ∈ pathPatterns 4 4 [1], HasCheckedCertificate 12 7 ([[], [1]] ++ P) := by
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
                exact k12t7_cover88
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover92
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t7_cover93
                    · exact by
                        intro _
                        exact k12t7_cover94
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover95
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t7_cover96
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover97
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover98
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover100
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover101
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover102
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover104 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 12 7 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p42, Certificates.k12t7p42_check⟩

private theorem k12t7_cover105 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 12 7 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p43, Certificates.k12t7p43_check⟩

private theorem k12t7_cover106 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 12 7 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover107 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 7 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover103 : ∀ P ∈ pathPatterns 3 3 [1, 1], HasCheckedCertificate 12 7 ([[], [1, 1]] ++ P) := by
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
                  exact k12t7_cover104
              · exact by
                  intro _
                  exact k12t7_cover105
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover106
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover107
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover109 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 7 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p44, Certificates.k12t7p44_check⟩

private theorem k12t7_cover108 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1], HasCheckedCertificate 12 7 ([[], [1, 1, 1]] ++ P) := by
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
        · exact by
            intro _
            exact k12t7_cover109

private theorem k12t7_cover110 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1], HasCheckedCertificate 12 7 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover111 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1], HasCheckedCertificate 12 7 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p45, Certificates.k12t7p45_check⟩

private theorem k12t7_cover112 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2], HasCheckedCertificate 12 7 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover113 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2], HasCheckedCertificate 12 7 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k12t7_cover114 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1], HasCheckedCertificate 12 7 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover115 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3], HasCheckedCertificate 12 7 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover117 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 7 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover116 : ∀ P ∈ pathPatterns 3 2 [1, 2], HasCheckedCertificate 12 7 ([[], [1, 2]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover117
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover118 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1], HasCheckedCertificate 12 7 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k12t7_cover119 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2], HasCheckedCertificate 12 7 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover120 : ∀ P ∈ pathPatterns 3 1 [1, 3], HasCheckedCertificate 12 7 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover121 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1], HasCheckedCertificate 12 7 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover122 : ∀ P ∈ pathPatterns 3 0 [1, 4], HasCheckedCertificate 12 7 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover124 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 12 7 ([[], [2], [2]] ++ P) := by
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

private theorem k12t7_cover125 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 12 7 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover123 : ∀ P ∈ pathPatterns 4 3 [2], HasCheckedCertificate 12 7 ([[], [2]] ++ P) := by
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
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover124
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover125
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover126 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2], HasCheckedCertificate 12 7 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover127 : ∀ P ∈ pathPatterns 3 1 [2, 2], HasCheckedCertificate 12 7 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover128 : ∀ P ∈ pathPatterns 3 0 [2, 3], HasCheckedCertificate 12 7 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover129 : ∀ P ∈ pathPatterns 4 2 [3], HasCheckedCertificate 12 7 ([[], [3]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover130 : ∀ P ∈ pathPatterns 4 1 [4], HasCheckedCertificate 12 7 ([[], [4]] ++ P) := by
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

private theorem k12t7_cover131 : ∀ P ∈ pathPatterns 4 0 [5], HasCheckedCertificate 12 7 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_seq4 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 7 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t7_cover5
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover87
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover103
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover108
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover110
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k12t7_cover111
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover112
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover113
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover114
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover115
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover116
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover118
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover119
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover120
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover121
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover122
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover123
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
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover126
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover127
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
                  exact k12t7_cover128
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover129
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
            exact k12t7_cover130
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
            exact k12t7_cover131
        · intro q
          exact Fin.elim0 q

private theorem k12t7_cover3 : ∀ P ∈ pathPatterns 6 5 [], HasCheckedCertificate 12 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t7_seq4


private theorem k12t7_cover134 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 12 7 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover135 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 12 7 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p46, Certificates.k12t7p46_check⟩

private theorem k12t7_cover136 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 12 7 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p47, Certificates.k12t7p47_check⟩

private theorem k12t7_cover137 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 12 7 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover138 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 7 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover133 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 12 7 ([[1], [1]] ++ P) := by
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
                exact k12t7_cover134
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t7_cover135
              · exact by
                  intro _
                  exact k12t7_cover136
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover137
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover138
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover140 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 7 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p48, Certificates.k12t7p48_check⟩

private theorem k12t7_cover139 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 12 7 ([[1], [1, 1]] ++ P) := by
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
            exact k12t7_cover140

private theorem k12t7_cover141 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 12 7 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover142 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 12 7 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p49, Certificates.k12t7p49_check⟩

private theorem k12t7_cover143 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 12 7 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover144 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 12 7 ([[1], [1, 2]] ++ P) := by
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

private theorem k12t7_cover145 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 12 7 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover146 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 12 7 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover148 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 7 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover147 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 12 7 ([[1], [2]] ++ P) := by
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
                exact k12t7_cover148
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover149 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 12 7 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover150 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 12 7 ([[1], [3]] ++ P) := by
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

private theorem k12t7_cover151 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 12 7 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover132 : ∀ P ∈ pathPatterns 5 4 [1], HasCheckedCertificate 12 7 ([[1]] ++ P) := by
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
                exact k12t7_cover133
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover139
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t7_cover141
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k12t7_cover142
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t7_cover143
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover144
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t7_cover145
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover146
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover147
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover149
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover150
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover151
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover153 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 12 7 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover154 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 12 7 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t7p50, Certificates.k12t7p50_check⟩

private theorem k12t7_cover155 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 12 7 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover156 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 12 7 ([[1, 1], [2]] ++ P) := by
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

private theorem k12t7_cover157 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 12 7 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover152 : ∀ P ∈ pathPatterns 4 3 [1, 1], HasCheckedCertificate 12 7 ([[1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover153
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t7_cover154
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t7_cover155
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover156
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover157
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover159 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 7 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover158 : ∀ P ∈ pathPatterns 3 2 [1, 1, 1], HasCheckedCertificate 12 7 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover159
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover160 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 1], HasCheckedCertificate 12 7 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k12t7_cover161 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 1], HasCheckedCertificate 12 7 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t7_cover162 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 2], HasCheckedCertificate 12 7 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover163 : ∀ P ∈ pathPatterns 3 1 [1, 1, 2], HasCheckedCertificate 12 7 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover164 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 1], HasCheckedCertificate 12 7 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover165 : ∀ P ∈ pathPatterns 3 0 [1, 1, 3], HasCheckedCertificate 12 7 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover167 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 12 7 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover166 : ∀ P ∈ pathPatterns 4 2 [1, 2], HasCheckedCertificate 12 7 ([[1, 2]] ++ P) := by
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
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover167
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover168 : ∀ P ∈ pathPatterns 3 1 [1, 2, 1], HasCheckedCertificate 12 7 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover169 : ∀ P ∈ pathPatterns 3 0 [1, 2, 2], HasCheckedCertificate 12 7 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover170 : ∀ P ∈ pathPatterns 4 1 [1, 3], HasCheckedCertificate 12 7 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover171 : ∀ P ∈ pathPatterns 3 0 [1, 3, 1], HasCheckedCertificate 12 7 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover172 : ∀ P ∈ pathPatterns 4 0 [1, 4], HasCheckedCertificate 12 7 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover174 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 12 7 ([[2], [2]] ++ P) := by
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

private theorem k12t7_cover175 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 12 7 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover173 : ∀ P ∈ pathPatterns 5 3 [2], HasCheckedCertificate 12 7 ([[2]] ++ P) := by
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
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover174
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t7_cover175
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover176 : ∀ P ∈ pathPatterns 3 0 [2, 1, 2], HasCheckedCertificate 12 7 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover177 : ∀ P ∈ pathPatterns 4 1 [2, 2], HasCheckedCertificate 12 7 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover178 : ∀ P ∈ pathPatterns 4 0 [2, 3], HasCheckedCertificate 12 7 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_cover179 : ∀ P ∈ pathPatterns 5 2 [3], HasCheckedCertificate 12 7 ([[3]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t7_cover180 : ∀ P ∈ pathPatterns 5 1 [4], HasCheckedCertificate 12 7 ([[4]] ++ P) := by
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

private theorem k12t7_cover181 : ∀ P ∈ pathPatterns 5 0 [5], HasCheckedCertificate 12 7 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t7_seq2 : amountSequenceForall 6 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 12 7 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k12t7_cover3
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover132
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover152
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover158
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover160
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro _
                                    exact k12t7_cover161
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover162
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover163
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k12t7_cover164
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover165
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover166
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover168
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover169
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover170
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover171
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover172
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover173
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
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k12t7_cover176
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k12t7_cover177
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
                  exact k12t7_cover178
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k12t7_cover179
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
            exact k12t7_cover180
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
            exact k12t7_cover181
        · intro q
          exact Fin.elim0 q

private theorem k12t7_cover1 : ∀ P ∈ pathPatterns 7 5 [], HasCheckedCertificate 12 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k12t7_seq2


theorem coverage_k12_t7 :
    ∀ P ∈ pathPatterns 7 5, HasCheckedCertificate 12 7 P :=
  k12t7_cover1

private theorem k12t8_cover9 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p0, Certificates.k12t8p0_check⟩

private theorem k12t8_cover8 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k12t8_cover9

private theorem k12t8_cover10 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p1, Certificates.k12t8p1_check⟩

private theorem k12t8_cover11 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p2, Certificates.k12t8p2_check⟩

private theorem k12t8_cover12 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p3, Certificates.k12t8p3_check⟩

private theorem k12t8_cover13 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 12 8 ([[], [], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p4, Certificates.k12t8p4_check⟩

private theorem k12t8_cover7 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 12 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover8
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k12t8_cover10
        · exact by
            intro _
            exact k12t8_cover11
        · exact by
            intro _
            exact k12t8_cover12
        · exact by
            intro _
            exact k12t8_cover13

private theorem k12t8_cover14 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 12 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover15 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 12 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p5, Certificates.k12t8p5_check⟩

private theorem k12t8_cover16 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 12 8 ([[], [], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p6, Certificates.k12t8p6_check⟩

private theorem k12t8_cover17 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 12 8 ([[], [], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p7, Certificates.k12t8p7_check⟩

private theorem k12t8_cover18 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 12 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover19 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 12 8 ([[], [], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p8, Certificates.k12t8p8_check⟩

private theorem k12t8_cover20 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 12 8 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover21 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 12 8 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover6 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 12 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover7
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover14
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t8_cover15
              · exact by
                  intro _
                  exact k12t8_cover16
              · exact by
                  intro _
                  exact k12t8_cover17
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover18
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k12t8_cover19
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover20
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover21
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover23 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 12 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p9, Certificates.k12t8p9_check⟩

private theorem k12t8_cover24 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 12 8 ([[], [], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p10, Certificates.k12t8p10_check⟩

private theorem k12t8_cover25 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 12 8 ([[], [], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p11, Certificates.k12t8p11_check⟩

private theorem k12t8_cover22 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 12 8 ([[], [], [], [], [1]] ++ P) := by
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
            exact k12t8_cover23
        · exact by
            intro _
            exact k12t8_cover24
        · exact by
            intro _
            exact k12t8_cover25

private theorem k12t8_cover26 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover27 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p12, Certificates.k12t8p12_check⟩

private theorem k12t8_cover28 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p13, Certificates.k12t8p13_check⟩

private theorem k12t8_cover29 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover30 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p14, Certificates.k12t8p14_check⟩

private theorem k12t8_cover31 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 12 8 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover33 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 8 ([[], [], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p15, Certificates.k12t8p15_check⟩

private theorem k12t8_cover32 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 12 8 ([[], [], [], [], [2]] ++ P) := by
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
            exact k12t8_cover33

private theorem k12t8_cover34 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 12 8 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover35 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 12 8 ([[], [], [], [], [3]] ++ P) := by
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

private theorem k12t8_cover36 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 12 8 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover5 : ∀ P ∈ pathPatterns 4 4 [], HasCheckedCertificate 12 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover22
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover26
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t8_cover27
                    · exact by
                        intro _
                        exact k12t8_cover28
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover29
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t8_cover30
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover31
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover32
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
                      exact k12t8_cover34
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover35
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
                exact k12t8_cover36
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover38 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 12 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover39 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 12 8 ([[], [], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p16, Certificates.k12t8p16_check⟩

private theorem k12t8_cover40 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 12 8 ([[], [], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p17, Certificates.k12t8p17_check⟩

private theorem k12t8_cover41 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 12 8 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover42 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 12 8 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover37 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 12 8 ([[], [], [], [1]] ++ P) := by
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
                exact k12t8_cover38
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t8_cover39
              · exact by
                  intro _
                  exact k12t8_cover40
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover41
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover42
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover44 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 8 ([[], [], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p18, Certificates.k12t8p18_check⟩

private theorem k12t8_cover43 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 12 8 ([[], [], [], [1, 1]] ++ P) := by
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
            exact k12t8_cover44

private theorem k12t8_cover45 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover46 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p19, Certificates.k12t8p19_check⟩

private theorem k12t8_cover47 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 12 8 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover48 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 12 8 ([[], [], [], [1, 2]] ++ P) := by
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

private theorem k12t8_cover49 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 12 8 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover50 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 12 8 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover52 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 8 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover51 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 12 8 ([[], [], [], [2]] ++ P) := by
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
                exact k12t8_cover52
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover53 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 12 8 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover54 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 12 8 ([[], [], [], [3]] ++ P) := by
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

private theorem k12t8_cover55 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 12 8 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover4 : ∀ P ∈ pathPatterns 5 4 [], HasCheckedCertificate 12 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover37
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover43
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover45
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k12t8_cover46
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover47
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover48
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover49
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover50
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover51
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
                      exact k12t8_cover53
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover54
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
                exact k12t8_cover55
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover58 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 12 8 ([[], [], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p20, Certificates.k12t8p20_check⟩

private theorem k12t8_cover59 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 12 8 ([[], [], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p21, Certificates.k12t8p21_check⟩

private theorem k12t8_cover57 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 12 8 ([[], [], [1], [1]] ++ P) := by
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
            exact k12t8_cover58
        · exact by
            intro _
            exact k12t8_cover59

private theorem k12t8_cover60 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 12 8 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover61 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p22, Certificates.k12t8p22_check⟩

private theorem k12t8_cover62 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 12 8 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover63 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 12 8 ([[], [], [1], [2]] ++ P) := by
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

private theorem k12t8_cover64 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 12 8 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover56 : ∀ P ∈ pathPatterns 4 3 [1], HasCheckedCertificate 12 8 ([[], [], [1]] ++ P) := by
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
                exact k12t8_cover57
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover60
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k12t8_cover61
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover62
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover63
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
                exact k12t8_cover64
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover66 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 12 8 ([[], [], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p23, Certificates.k12t8p23_check⟩

private theorem k12t8_cover67 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 8 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover65 : ∀ P ∈ pathPatterns 3 2 [1, 1], HasCheckedCertificate 12 8 ([[], [], [1, 1]] ++ P) := by
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
                  exact k12t8_cover66
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover67
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover68 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [1, 1, 1]] ++ P) := by
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

private theorem k12t8_cover69 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1], HasCheckedCertificate 12 8 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover70 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2], HasCheckedCertificate 12 8 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover71 : ∀ P ∈ pathPatterns 3 1 [1, 2], HasCheckedCertificate 12 8 ([[], [], [1, 2]] ++ P) := by
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

private theorem k12t8_cover72 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1], HasCheckedCertificate 12 8 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover73 : ∀ P ∈ pathPatterns 3 0 [1, 3], HasCheckedCertificate 12 8 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover75 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 12 8 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover74 : ∀ P ∈ pathPatterns 4 2 [2], HasCheckedCertificate 12 8 ([[], [], [2]] ++ P) := by
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
                exact k12t8_cover75
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover76 : ∀ P ∈ pathPatterns 3 0 [2, 2], HasCheckedCertificate 12 8 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover77 : ∀ P ∈ pathPatterns 4 1 [3], HasCheckedCertificate 12 8 ([[], [], [3]] ++ P) := by
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

private theorem k12t8_cover78 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 12 8 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover3 : ∀ P ∈ pathPatterns 6 4 [], HasCheckedCertificate 12 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover56
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover65
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover68
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k12t8_cover69
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover70
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover71
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover72
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover73
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover74
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
                      exact k12t8_cover76
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover77
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
                exact k12t8_cover78
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover81 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 12 8 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover82 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 12 8 ([[], [1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p24, Certificates.k12t8p24_check⟩

private theorem k12t8_cover83 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 12 8 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover80 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 12 8 ([[], [1], [1]] ++ P) := by
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
                exact k12t8_cover81
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k12t8_cover82
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover83
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover84 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 12 8 ([[], [1], [1, 1]] ++ P) := by
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

private theorem k12t8_cover85 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover86 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 12 8 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover87 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 12 8 ([[], [1], [2]] ++ P) := by
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

private theorem k12t8_cover88 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 12 8 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover79 : ∀ P ∈ pathPatterns 5 3 [1], HasCheckedCertificate 12 8 ([[], [1]] ++ P) := by
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
                exact k12t8_cover80
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover84
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover85
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover86
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover87
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
                exact k12t8_cover88
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover90 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 12 8 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover91 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 12 8 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover89 : ∀ P ∈ pathPatterns 4 2 [1, 1], HasCheckedCertificate 12 8 ([[], [1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover90
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover91
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover92 : ∀ P ∈ pathPatterns 3 1 [1, 1, 1], HasCheckedCertificate 12 8 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover93 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 1], HasCheckedCertificate 12 8 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover94 : ∀ P ∈ pathPatterns 3 0 [1, 1, 2], HasCheckedCertificate 12 8 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover95 : ∀ P ∈ pathPatterns 4 1 [1, 2], HasCheckedCertificate 12 8 ([[], [1, 2]] ++ P) := by
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

private theorem k12t8_cover96 : ∀ P ∈ pathPatterns 3 0 [1, 2, 1], HasCheckedCertificate 12 8 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover97 : ∀ P ∈ pathPatterns 4 0 [1, 3], HasCheckedCertificate 12 8 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover99 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 12 8 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover98 : ∀ P ∈ pathPatterns 5 2 [2], HasCheckedCertificate 12 8 ([[], [2]] ++ P) := by
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
                exact k12t8_cover99
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover100 : ∀ P ∈ pathPatterns 4 0 [2, 2], HasCheckedCertificate 12 8 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover101 : ∀ P ∈ pathPatterns 5 1 [3], HasCheckedCertificate 12 8 ([[], [3]] ++ P) := by
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

private theorem k12t8_cover102 : ∀ P ∈ pathPatterns 5 0 [4], HasCheckedCertificate 12 8 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover2 : ∀ P ∈ pathPatterns 7 4 [], HasCheckedCertificate 12 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover79
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover89
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover92
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k12t8_cover93
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover94
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover95
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover96
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover97
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover98
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
                      exact k12t8_cover100
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover101
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
                exact k12t8_cover102
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover106 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 12 8 ([[1], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k12t8p25, Certificates.k12t8p25_check⟩

private theorem k12t8_cover105 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 12 8 ([[1], [1], [1]] ++ P) := by
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
            exact k12t8_cover106

private theorem k12t8_cover107 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 12 8 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k12t8_cover108 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 12 8 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover104 : ∀ P ∈ pathPatterns 4 2 [1], HasCheckedCertificate 12 8 ([[1], [1]] ++ P) := by
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
                exact k12t8_cover105
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover107
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover108
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover109 : ∀ P ∈ pathPatterns 3 1 [1, 1], HasCheckedCertificate 12 8 ([[1], [1, 1]] ++ P) := by
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

private theorem k12t8_cover110 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1], HasCheckedCertificate 12 8 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover111 : ∀ P ∈ pathPatterns 3 0 [1, 2], HasCheckedCertificate 12 8 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover112 : ∀ P ∈ pathPatterns 4 1 [2], HasCheckedCertificate 12 8 ([[1], [2]] ++ P) := by
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

private theorem k12t8_cover113 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 12 8 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover103 : ∀ P ∈ pathPatterns 6 3 [1], HasCheckedCertificate 12 8 ([[1]] ++ P) := by
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
                exact k12t8_cover104
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover109
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover110
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover111
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover112
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
                exact k12t8_cover113
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover115 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 12 8 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover116 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 12 8 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover114 : ∀ P ∈ pathPatterns 5 2 [1, 1], HasCheckedCertificate 12 8 ([[1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover115
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover116
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover117 : ∀ P ∈ pathPatterns 4 1 [1, 1, 1], HasCheckedCertificate 12 8 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover118 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1, 1], HasCheckedCertificate 12 8 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover119 : ∀ P ∈ pathPatterns 4 0 [1, 1, 2], HasCheckedCertificate 12 8 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover120 : ∀ P ∈ pathPatterns 5 1 [1, 2], HasCheckedCertificate 12 8 ([[1, 2]] ++ P) := by
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

private theorem k12t8_cover121 : ∀ P ∈ pathPatterns 4 0 [1, 2, 1], HasCheckedCertificate 12 8 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover122 : ∀ P ∈ pathPatterns 5 0 [1, 3], HasCheckedCertificate 12 8 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover124 : ∀ P ∈ pathPatterns 4 0 [2], HasCheckedCertificate 12 8 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover123 : ∀ P ∈ pathPatterns 6 2 [2], HasCheckedCertificate 12 8 ([[2]] ++ P) := by
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
                exact k12t8_cover124
            · intro q
              exact Fin.elim0 q

private theorem k12t8_cover125 : ∀ P ∈ pathPatterns 5 0 [2, 2], HasCheckedCertificate 12 8 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover126 : ∀ P ∈ pathPatterns 6 1 [3], HasCheckedCertificate 12 8 ([[3]] ++ P) := by
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

private theorem k12t8_cover127 : ∀ P ∈ pathPatterns 6 0 [4], HasCheckedCertificate 12 8 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k12t8_cover1 : ∀ P ∈ pathPatterns 8 4 [], HasCheckedCertificate 12 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k12t8_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover103
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover114
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover117
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k12t8_cover118
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover119
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover120
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k12t8_cover121
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k12t8_cover122
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover123
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
                      exact k12t8_cover125
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k12t8_cover126
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
                exact k12t8_cover127
            · intro q
              exact Fin.elim0 q

theorem coverage_k12_t8 :
    ∀ P ∈ pathPatterns 8 4, HasCheckedCertificate 12 8 P :=
  k12t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
