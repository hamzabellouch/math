import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK11
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k11t5_cover8 : ∀ P ∈ pathPatterns 0 6 [], HasCheckedCertificate 11 5 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p0, Certificates.k11t5p0_check⟩

private theorem k11t5_cover7 : ∀ P ∈ pathPatterns 1 6 [], HasCheckedCertificate 11 5 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k11t5_cover8

private theorem k11t5_cover9 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 11 5 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p1, Certificates.k11t5p1_check⟩

private theorem k11t5_cover10 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 11 5 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p2, Certificates.k11t5p2_check⟩

private theorem k11t5_cover11 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 11 5 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p3, Certificates.k11t5p3_check⟩

private theorem k11t5_cover12 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 11 5 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p4, Certificates.k11t5p4_check⟩

private theorem k11t5_cover13 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 11 5 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p5, Certificates.k11t5p5_check⟩

private theorem k11t5_cover14 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 11 5 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p6, Certificates.k11t5p6_check⟩

private theorem k11t5_cover6 : ∀ P ∈ pathPatterns 2 6 [], HasCheckedCertificate 11 5 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t5_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k11t5_cover9
        · exact by
            intro _
            exact k11t5_cover10
        · exact by
            intro _
            exact k11t5_cover11
        · exact by
            intro _
            exact k11t5_cover12
        · exact by
            intro _
            exact k11t5_cover13
        · exact by
            intro _
            exact k11t5_cover14

private theorem k11t5_cover15 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 11 5 ([[], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover16 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 11 5 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p7, Certificates.k11t5p7_check⟩

private theorem k11t5_cover17 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 11 5 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p8, Certificates.k11t5p8_check⟩

private theorem k11t5_cover18 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 11 5 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p9, Certificates.k11t5p9_check⟩

private theorem k11t5_cover19 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 11 5 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p10, Certificates.k11t5p10_check⟩

private theorem k11t5_cover20 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 11 5 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p11, Certificates.k11t5p11_check⟩

private theorem k11t5_cover21 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 11 5 ([[], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover22 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 11 5 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p12, Certificates.k11t5p12_check⟩

private theorem k11t5_cover23 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 11 5 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p13, Certificates.k11t5p13_check⟩

private theorem k11t5_cover24 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 11 5 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p14, Certificates.k11t5p14_check⟩

private theorem k11t5_cover25 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 11 5 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover26 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 11 5 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p15, Certificates.k11t5p15_check⟩

private theorem k11t5_cover27 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 11 5 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover28 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 11 5 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover29 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 11 5 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover5 : ∀ P ∈ pathPatterns 3 6 [], HasCheckedCertificate 11 5 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t5_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover15
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t5_cover16
              · exact by
                  intro _
                  exact k11t5_cover17
              · exact by
                  intro _
                  exact k11t5_cover18
              · exact by
                  intro _
                  exact k11t5_cover19
              · exact by
                  intro _
                  exact k11t5_cover20
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover21
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t5_cover22
              · exact by
                  intro _
                  exact k11t5_cover23
              · exact by
                  intro _
                  exact k11t5_cover24
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover25
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
                  exact k11t5_cover26
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover27
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
                exact k11t5_cover28
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover29
            · intro q
              exact Fin.elim0 q

private theorem k11t5_cover31 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 11 5 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p16, Certificates.k11t5p16_check⟩

private theorem k11t5_cover32 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 11 5 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p17, Certificates.k11t5p17_check⟩

private theorem k11t5_cover33 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 11 5 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p18, Certificates.k11t5p18_check⟩

private theorem k11t5_cover34 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 11 5 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p19, Certificates.k11t5p19_check⟩

private theorem k11t5_cover35 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 11 5 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p20, Certificates.k11t5p20_check⟩

private theorem k11t5_cover30 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 11 5 ([[], [1]] ++ P) := by
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
            exact k11t5_cover31
        · exact by
            intro _
            exact k11t5_cover32
        · exact by
            intro _
            exact k11t5_cover33
        · exact by
            intro _
            exact k11t5_cover34
        · exact by
            intro _
            exact k11t5_cover35

private theorem k11t5_cover36 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 11 5 ([[], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover37 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 11 5 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p21, Certificates.k11t5p21_check⟩

private theorem k11t5_cover38 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 11 5 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p22, Certificates.k11t5p22_check⟩

private theorem k11t5_cover39 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 11 5 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p23, Certificates.k11t5p23_check⟩

private theorem k11t5_cover40 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 11 5 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p24, Certificates.k11t5p24_check⟩

private theorem k11t5_cover41 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 11 5 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover42 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 11 5 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p25, Certificates.k11t5p25_check⟩

private theorem k11t5_cover43 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 11 5 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p26, Certificates.k11t5p26_check⟩

private theorem k11t5_cover44 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 11 5 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p27, Certificates.k11t5p27_check⟩

private theorem k11t5_cover45 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 11 5 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover46 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 11 5 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p28, Certificates.k11t5p28_check⟩

private theorem k11t5_cover47 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 11 5 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p29, Certificates.k11t5p29_check⟩

private theorem k11t5_cover48 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 11 5 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover49 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 11 5 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p30, Certificates.k11t5p30_check⟩

private theorem k11t5_cover50 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 11 5 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover52 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 11 5 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p31, Certificates.k11t5p31_check⟩

private theorem k11t5_cover53 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 11 5 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p32, Certificates.k11t5p32_check⟩

private theorem k11t5_cover54 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 11 5 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p33, Certificates.k11t5p33_check⟩

private theorem k11t5_cover51 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 11 5 ([[], [2]] ++ P) := by
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
            exact k11t5_cover52
        · exact by
            intro _
            exact k11t5_cover53
        · exact by
            intro _
            exact k11t5_cover54

private theorem k11t5_cover55 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 11 5 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p34, Certificates.k11t5p34_check⟩

private theorem k11t5_cover56 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 11 5 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p35, Certificates.k11t5p35_check⟩

private theorem k11t5_cover57 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 11 5 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover58 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 11 5 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p36, Certificates.k11t5p36_check⟩

private theorem k11t5_cover59 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 11 5 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover60 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 11 5 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover62 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 5 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p37, Certificates.k11t5p37_check⟩

private theorem k11t5_cover61 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 11 5 ([[], [3]] ++ P) := by
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
            exact k11t5_cover62

private theorem k11t5_cover63 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 11 5 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover64 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 11 5 ([[], [4]] ++ P) := by
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

private theorem k11t5_cover65 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 11 5 ([[], [5]] ++ P) := by
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

private theorem k11t5_cover66 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 11 5 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t5_seq4 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 11 5 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t5_cover5
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover30
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover36
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover37
                · exact by
                    intro _
                    exact k11t5_cover38
                · exact by
                    intro _
                    exact k11t5_cover39
                · exact by
                    intro _
                    exact k11t5_cover40
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover41
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover42
                · exact by
                    intro _
                    exact k11t5_cover43
                · exact by
                    intro _
                    exact k11t5_cover44
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover45
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover46
                · exact by
                    intro _
                    exact k11t5_cover47
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover48
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover49
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover50
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover51
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
                    exact k11t5_cover55
                · exact by
                    intro _
                    exact k11t5_cover56
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover57
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k11t5_cover58
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover59
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover60
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover61
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
                  exact k11t5_cover63
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover64
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
            exact k11t5_cover65
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
            exact k11t5_cover66
        · intro q
          exact Fin.elim0 q

private theorem k11t5_cover3 : ∀ P ∈ pathPatterns 4 6 [], HasCheckedCertificate 11 5 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k11t5_seq4


private theorem k11t5_cover69 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 11 5 ([[1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover70 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 11 5 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p38, Certificates.k11t5p38_check⟩

private theorem k11t5_cover71 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 11 5 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p39, Certificates.k11t5p39_check⟩

private theorem k11t5_cover72 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 11 5 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p40, Certificates.k11t5p40_check⟩

private theorem k11t5_cover73 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 11 5 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p41, Certificates.k11t5p41_check⟩

private theorem k11t5_cover74 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 11 5 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover75 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 11 5 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p42, Certificates.k11t5p42_check⟩

private theorem k11t5_cover76 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 11 5 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p43, Certificates.k11t5p43_check⟩

private theorem k11t5_cover77 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 11 5 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover78 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 11 5 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover79 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 11 5 ([[1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover68 : ∀ P ∈ pathPatterns 3 5 [1], HasCheckedCertificate 11 5 ([[1]] ++ P) := by
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
                exact k11t5_cover69
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t5_cover70
              · exact by
                  intro _
                  exact k11t5_cover71
              · exact by
                  intro _
                  exact k11t5_cover72
              · exact by
                  intro _
                  exact k11t5_cover73
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover74
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t5_cover75
              · exact by
                  intro _
                  exact k11t5_cover76
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover77
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
                exact k11t5_cover78
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover79
            · intro q
              exact Fin.elim0 q

private theorem k11t5_cover81 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 11 5 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p44, Certificates.k11t5p44_check⟩

private theorem k11t5_cover82 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 11 5 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p45, Certificates.k11t5p45_check⟩

private theorem k11t5_cover83 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 11 5 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p46, Certificates.k11t5p46_check⟩

private theorem k11t5_cover80 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 11 5 ([[1, 1]] ++ P) := by
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
            exact k11t5_cover81
        · exact by
            intro _
            exact k11t5_cover82
        · exact by
            intro _
            exact k11t5_cover83

private theorem k11t5_cover84 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 11 5 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover85 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 11 5 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p47, Certificates.k11t5p47_check⟩

private theorem k11t5_cover86 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 11 5 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p48, Certificates.k11t5p48_check⟩

private theorem k11t5_cover87 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 11 5 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p49, Certificates.k11t5p49_check⟩

private theorem k11t5_cover88 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 11 5 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover89 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 11 5 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p50, Certificates.k11t5p50_check⟩

private theorem k11t5_cover90 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 11 5 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p51, Certificates.k11t5p51_check⟩

private theorem k11t5_cover91 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 11 5 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover92 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 11 5 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p52, Certificates.k11t5p52_check⟩

private theorem k11t5_cover93 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 11 5 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover95 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 5 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p53, Certificates.k11t5p53_check⟩

private theorem k11t5_cover96 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 5 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p54, Certificates.k11t5p54_check⟩

private theorem k11t5_cover94 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 11 5 ([[1, 2]] ++ P) := by
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
            exact k11t5_cover95
        · exact by
            intro _
            exact k11t5_cover96

private theorem k11t5_cover97 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 11 5 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover98 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 11 5 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p55, Certificates.k11t5p55_check⟩

private theorem k11t5_cover99 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 11 5 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover100 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 11 5 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p56, Certificates.k11t5p56_check⟩

private theorem k11t5_cover101 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 11 5 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover103 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 5 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p57, Certificates.k11t5p57_check⟩

private theorem k11t5_cover102 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 11 5 ([[1, 3]] ++ P) := by
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
            exact k11t5_cover103

private theorem k11t5_cover104 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 11 5 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover105 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 11 5 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover106 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 11 5 ([[1, 4]] ++ P) := by
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

private theorem k11t5_cover107 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 11 5 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover108 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 11 5 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t5_seq67 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 11 5 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t5_cover68
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover80
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover84
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover85
                · exact by
                    intro _
                    exact k11t5_cover86
                · exact by
                    intro _
                    exact k11t5_cover87
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover88
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover89
                · exact by
                    intro _
                    exact k11t5_cover90
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover91
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover92
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover93
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover94
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover97
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k11t5_cover98
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover99
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t5_cover100
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover101
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover102
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover104
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover105
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover106
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover107
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover108
        · intro q
          exact Fin.elim0 q

private theorem k11t5_cover110 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 11 5 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover111 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 11 5 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p58, Certificates.k11t5p58_check⟩

private theorem k11t5_cover112 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 11 5 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover113 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 11 5 ([[2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover109 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 11 5 ([[2]] ++ P) := by
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
                exact k11t5_cover110
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t5_cover111
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover112
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t5_cover113
            · intro q
              exact Fin.elim0 q

private theorem k11t5_cover114 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 11 5 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t5p59, Certificates.k11t5p59_check⟩

private theorem k11t5_cover115 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 11 5 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover116 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 11 5 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover117 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 11 5 ([[2, 2]] ++ P) := by
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

private theorem k11t5_cover118 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 11 5 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover119 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 11 5 ([[2, 3]] ++ P) := by
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

private theorem k11t5_cover120 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 11 5 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t5_cover122 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 11 5 ([[3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t5_cover121 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 11 5 ([[3]] ++ P) := by
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
                exact k11t5_cover122
            · intro q
              exact Fin.elim0 q

private theorem k11t5_cover123 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 11 5 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t5_cover124 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 11 5 ([[4]] ++ P) := by
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

private theorem k11t5_cover125 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 11 5 ([[5]] ++ P) := by
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

private theorem k11t5_cover126 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 11 5 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t5_seq2 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 11 5 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t5_cover3
  · intro q
    fin_cases q
    · exact k11t5_seq67

    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover109
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
                          exact k11t5_cover114
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t5_cover115
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t5_cover116
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover117
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
                        exact k11t5_cover118
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t5_cover119
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
                  exact k11t5_cover120
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover121
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
                  exact k11t5_cover123
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t5_cover124
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
            exact k11t5_cover125
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
            exact k11t5_cover126
        · intro q
          exact Fin.elim0 q

private theorem k11t5_cover1 : ∀ P ∈ pathPatterns 5 6 [], HasCheckedCertificate 11 5 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k11t5_seq2


theorem coverage_k11_t5 :
    ∀ P ∈ pathPatterns 5 6, HasCheckedCertificate 11 5 P :=
  k11t5_cover1

private theorem k11t6_cover10 : ∀ P ∈ pathPatterns 0 5 [], HasCheckedCertificate 11 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p0, Certificates.k11t6p0_check⟩

private theorem k11t6_cover9 : ∀ P ∈ pathPatterns 1 5 [], HasCheckedCertificate 11 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k11t6_cover10

private theorem k11t6_cover11 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 11 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p1, Certificates.k11t6p1_check⟩

private theorem k11t6_cover12 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 11 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p2, Certificates.k11t6p2_check⟩

private theorem k11t6_cover13 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 11 6 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p3, Certificates.k11t6p3_check⟩

private theorem k11t6_cover14 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 11 6 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p4, Certificates.k11t6p4_check⟩

private theorem k11t6_cover15 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 11 6 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p5, Certificates.k11t6p5_check⟩

private theorem k11t6_cover8 : ∀ P ∈ pathPatterns 2 5 [], HasCheckedCertificate 11 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t6_cover9
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k11t6_cover11
        · exact by
            intro _
            exact k11t6_cover12
        · exact by
            intro _
            exact k11t6_cover13
        · exact by
            intro _
            exact k11t6_cover14
        · exact by
            intro _
            exact k11t6_cover15

private theorem k11t6_cover16 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 11 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover17 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 11 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p6, Certificates.k11t6p6_check⟩

private theorem k11t6_cover18 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 11 6 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p7, Certificates.k11t6p7_check⟩

private theorem k11t6_cover19 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 11 6 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p8, Certificates.k11t6p8_check⟩

private theorem k11t6_cover20 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 11 6 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p9, Certificates.k11t6p9_check⟩

private theorem k11t6_cover21 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 11 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover22 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 11 6 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p10, Certificates.k11t6p10_check⟩

private theorem k11t6_cover23 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 11 6 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p11, Certificates.k11t6p11_check⟩

private theorem k11t6_cover24 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 11 6 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover25 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 11 6 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover26 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 11 6 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover7 : ∀ P ∈ pathPatterns 3 5 [], HasCheckedCertificate 11 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t6_cover8
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover16
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t6_cover17
              · exact by
                  intro _
                  exact k11t6_cover18
              · exact by
                  intro _
                  exact k11t6_cover19
              · exact by
                  intro _
                  exact k11t6_cover20
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover21
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t6_cover22
              · exact by
                  intro _
                  exact k11t6_cover23
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover24
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
                exact k11t6_cover25
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover26
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover28 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 11 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p12, Certificates.k11t6p12_check⟩

private theorem k11t6_cover29 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 11 6 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p13, Certificates.k11t6p13_check⟩

private theorem k11t6_cover30 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 11 6 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p14, Certificates.k11t6p14_check⟩

private theorem k11t6_cover31 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 11 6 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p15, Certificates.k11t6p15_check⟩

private theorem k11t6_cover27 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 11 6 ([[], [], [1]] ++ P) := by
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
            exact k11t6_cover28
        · exact by
            intro _
            exact k11t6_cover29
        · exact by
            intro _
            exact k11t6_cover30
        · exact by
            intro _
            exact k11t6_cover31

private theorem k11t6_cover32 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 11 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover33 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 11 6 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p16, Certificates.k11t6p16_check⟩

private theorem k11t6_cover34 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 11 6 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p17, Certificates.k11t6p17_check⟩

private theorem k11t6_cover35 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 11 6 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p18, Certificates.k11t6p18_check⟩

private theorem k11t6_cover36 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 11 6 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover37 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 11 6 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p19, Certificates.k11t6p19_check⟩

private theorem k11t6_cover38 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 11 6 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p20, Certificates.k11t6p20_check⟩

private theorem k11t6_cover39 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 11 6 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover40 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 11 6 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p21, Certificates.k11t6p21_check⟩

private theorem k11t6_cover41 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 11 6 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover43 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 6 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p22, Certificates.k11t6p22_check⟩

private theorem k11t6_cover44 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 6 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p23, Certificates.k11t6p23_check⟩

private theorem k11t6_cover42 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 11 6 ([[], [], [2]] ++ P) := by
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
            exact k11t6_cover43
        · exact by
            intro _
            exact k11t6_cover44

private theorem k11t6_cover45 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 11 6 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p24, Certificates.k11t6p24_check⟩

private theorem k11t6_cover46 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 11 6 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover47 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 11 6 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover48 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 11 6 ([[], [], [3]] ++ P) := by
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

private theorem k11t6_cover49 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 11 6 ([[], [], [4]] ++ P) := by
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

private theorem k11t6_cover50 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 11 6 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_seq6 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 11 6 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t6_cover7
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover27
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover32
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t6_cover33
                · exact by
                    intro _
                    exact k11t6_cover34
                · exact by
                    intro _
                    exact k11t6_cover35
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover36
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t6_cover37
                · exact by
                    intro _
                    exact k11t6_cover38
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover39
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k11t6_cover40
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover41
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover42
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
                    exact k11t6_cover45
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover46
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover47
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover48
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
            exact k11t6_cover49
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
            exact k11t6_cover50
        · intro q
          exact Fin.elim0 q

private theorem k11t6_cover5 : ∀ P ∈ pathPatterns 4 5 [], HasCheckedCertificate 11 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k11t6_seq6


private theorem k11t6_cover52 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 11 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover53 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 11 6 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p25, Certificates.k11t6p25_check⟩

private theorem k11t6_cover54 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 11 6 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p26, Certificates.k11t6p26_check⟩

private theorem k11t6_cover55 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 11 6 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p27, Certificates.k11t6p27_check⟩

private theorem k11t6_cover56 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 11 6 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover57 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 11 6 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p28, Certificates.k11t6p28_check⟩

private theorem k11t6_cover58 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 11 6 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover59 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 11 6 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover51 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 11 6 ([[], [1]] ++ P) := by
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
                exact k11t6_cover52
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t6_cover53
              · exact by
                  intro _
                  exact k11t6_cover54
              · exact by
                  intro _
                  exact k11t6_cover55
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover56
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t6_cover57
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover58
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover59
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover61 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 6 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p29, Certificates.k11t6p29_check⟩

private theorem k11t6_cover62 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 6 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p30, Certificates.k11t6p30_check⟩

private theorem k11t6_cover60 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 11 6 ([[], [1, 1]] ++ P) := by
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
            exact k11t6_cover61
        · exact by
            intro _
            exact k11t6_cover62

private theorem k11t6_cover63 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 11 6 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover64 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 11 6 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p31, Certificates.k11t6p31_check⟩

private theorem k11t6_cover65 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 11 6 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p32, Certificates.k11t6p32_check⟩

private theorem k11t6_cover66 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 11 6 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover67 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 11 6 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p33, Certificates.k11t6p33_check⟩

private theorem k11t6_cover68 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 11 6 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover70 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 6 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p34, Certificates.k11t6p34_check⟩

private theorem k11t6_cover69 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 11 6 ([[], [1, 2]] ++ P) := by
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
            exact k11t6_cover70

private theorem k11t6_cover71 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 11 6 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover72 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 11 6 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover73 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 11 6 ([[], [1, 3]] ++ P) := by
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

private theorem k11t6_cover74 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 11 6 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover75 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 11 6 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover77 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 11 6 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover78 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 11 6 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover76 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 11 6 ([[], [2]] ++ P) := by
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
                exact k11t6_cover77
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover78
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover79 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 11 6 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover80 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 11 6 ([[], [2, 2]] ++ P) := by
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

private theorem k11t6_cover81 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 11 6 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover82 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 11 6 ([[], [3]] ++ P) := by
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

private theorem k11t6_cover83 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 11 6 ([[], [4]] ++ P) := by
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

private theorem k11t6_cover84 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 11 6 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_seq4 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 11 6 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t6_cover5
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover51
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover60
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover63
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k11t6_cover64
                      · exact by
                          intro _
                          exact k11t6_cover65
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover66
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k11t6_cover67
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover68
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover69
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover71
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover72
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover73
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover74
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover75
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover76
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
                        exact k11t6_cover79
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover80
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
                  exact k11t6_cover81
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover82
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
            exact k11t6_cover83
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
            exact k11t6_cover84
        · intro q
          exact Fin.elim0 q

private theorem k11t6_cover3 : ∀ P ∈ pathPatterns 5 5 [], HasCheckedCertificate 11 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k11t6_seq4


private theorem k11t6_cover87 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 11 6 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p35, Certificates.k11t6p35_check⟩

private theorem k11t6_cover88 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 6 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p36, Certificates.k11t6p36_check⟩

private theorem k11t6_cover89 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 6 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p37, Certificates.k11t6p37_check⟩

private theorem k11t6_cover86 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 11 6 ([[1], [1]] ++ P) := by
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
            exact k11t6_cover87
        · exact by
            intro _
            exact k11t6_cover88
        · exact by
            intro _
            exact k11t6_cover89

private theorem k11t6_cover90 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 11 6 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover91 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 11 6 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p38, Certificates.k11t6p38_check⟩

private theorem k11t6_cover92 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 11 6 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p39, Certificates.k11t6p39_check⟩

private theorem k11t6_cover93 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 11 6 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover94 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 11 6 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p40, Certificates.k11t6p40_check⟩

private theorem k11t6_cover95 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 11 6 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover97 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 6 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p41, Certificates.k11t6p41_check⟩

private theorem k11t6_cover96 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 11 6 ([[1], [2]] ++ P) := by
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
            exact k11t6_cover97

private theorem k11t6_cover98 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 11 6 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover99 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 11 6 ([[1], [3]] ++ P) := by
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

private theorem k11t6_cover100 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 11 6 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover85 : ∀ P ∈ pathPatterns 4 4 [1], HasCheckedCertificate 11 6 ([[1]] ++ P) := by
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
                exact k11t6_cover86
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t6_cover90
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t6_cover91
                    · exact by
                        intro _
                        exact k11t6_cover92
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t6_cover93
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t6_cover94
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t6_cover95
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover96
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
                      exact k11t6_cover98
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover99
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
                exact k11t6_cover100
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover102 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 11 6 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p42, Certificates.k11t6p42_check⟩

private theorem k11t6_cover103 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 11 6 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p43, Certificates.k11t6p43_check⟩

private theorem k11t6_cover104 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 11 6 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover105 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 11 6 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover101 : ∀ P ∈ pathPatterns 3 3 [1, 1], HasCheckedCertificate 11 6 ([[1, 1]] ++ P) := by
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
                  exact k11t6_cover102
              · exact by
                  intro _
                  exact k11t6_cover103
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover104
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t6_cover105
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover107 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 6 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p44, Certificates.k11t6p44_check⟩

private theorem k11t6_cover106 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1], HasCheckedCertificate 11 6 ([[1, 1, 1]] ++ P) := by
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
            exact k11t6_cover107

private theorem k11t6_cover108 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1], HasCheckedCertificate 11 6 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover109 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1], HasCheckedCertificate 11 6 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t6p45, Certificates.k11t6p45_check⟩

private theorem k11t6_cover110 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2], HasCheckedCertificate 11 6 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover111 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2], HasCheckedCertificate 11 6 ([[1, 1, 2]] ++ P) := by
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

private theorem k11t6_cover112 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1], HasCheckedCertificate 11 6 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover113 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3], HasCheckedCertificate 11 6 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover115 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 11 6 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t6_cover114 : ∀ P ∈ pathPatterns 3 2 [1, 2], HasCheckedCertificate 11 6 ([[1, 2]] ++ P) := by
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
                exact k11t6_cover115
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover116 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1], HasCheckedCertificate 11 6 ([[1, 2, 1]] ++ P) := by
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

private theorem k11t6_cover117 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2], HasCheckedCertificate 11 6 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover118 : ∀ P ∈ pathPatterns 3 1 [1, 3], HasCheckedCertificate 11 6 ([[1, 3]] ++ P) := by
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

private theorem k11t6_cover119 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1], HasCheckedCertificate 11 6 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover120 : ∀ P ∈ pathPatterns 3 0 [1, 4], HasCheckedCertificate 11 6 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover122 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 11 6 ([[2], [2]] ++ P) := by
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

private theorem k11t6_cover123 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 11 6 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover121 : ∀ P ∈ pathPatterns 4 3 [2], HasCheckedCertificate 11 6 ([[2]] ++ P) := by
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
                exact k11t6_cover122
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
                exact k11t6_cover123
            · intro q
              exact Fin.elim0 q

private theorem k11t6_cover124 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2], HasCheckedCertificate 11 6 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover125 : ∀ P ∈ pathPatterns 3 1 [2, 2], HasCheckedCertificate 11 6 ([[2, 2]] ++ P) := by
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

private theorem k11t6_cover126 : ∀ P ∈ pathPatterns 3 0 [2, 3], HasCheckedCertificate 11 6 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_cover127 : ∀ P ∈ pathPatterns 4 2 [3], HasCheckedCertificate 11 6 ([[3]] ++ P) := by
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

private theorem k11t6_cover128 : ∀ P ∈ pathPatterns 4 1 [4], HasCheckedCertificate 11 6 ([[4]] ++ P) := by
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

private theorem k11t6_cover129 : ∀ P ∈ pathPatterns 4 0 [5], HasCheckedCertificate 11 6 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t6_seq2 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 11 6 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k11t6_cover3
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover85
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover101
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover106
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k11t6_cover108
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k11t6_cover109
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k11t6_cover110
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover111
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k11t6_cover112
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover113
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover114
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover116
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
                        exact k11t6_cover117
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover118
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k11t6_cover119
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover120
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover121
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
                        exact k11t6_cover124
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k11t6_cover125
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
                  exact k11t6_cover126
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k11t6_cover127
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
            exact k11t6_cover128
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
            exact k11t6_cover129
        · intro q
          exact Fin.elim0 q

private theorem k11t6_cover1 : ∀ P ∈ pathPatterns 6 5 [], HasCheckedCertificate 11 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k11t6_seq2


theorem coverage_k11_t6 :
    ∀ P ∈ pathPatterns 6 5, HasCheckedCertificate 11 6 P :=
  k11t6_cover1

private theorem k11t7_cover8 : ∀ P ∈ pathPatterns 0 4 [], HasCheckedCertificate 11 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p0, Certificates.k11t7p0_check⟩

private theorem k11t7_cover7 : ∀ P ∈ pathPatterns 1 4 [], HasCheckedCertificate 11 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k11t7_cover8

private theorem k11t7_cover9 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 11 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p1, Certificates.k11t7p1_check⟩

private theorem k11t7_cover10 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 11 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p2, Certificates.k11t7p2_check⟩

private theorem k11t7_cover11 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 11 7 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p3, Certificates.k11t7p3_check⟩

private theorem k11t7_cover12 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 11 7 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p4, Certificates.k11t7p4_check⟩

private theorem k11t7_cover6 : ∀ P ∈ pathPatterns 2 4 [], HasCheckedCertificate 11 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover7
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k11t7_cover9
        · exact by
            intro _
            exact k11t7_cover10
        · exact by
            intro _
            exact k11t7_cover11
        · exact by
            intro _
            exact k11t7_cover12

private theorem k11t7_cover13 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 11 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover14 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 11 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p5, Certificates.k11t7p5_check⟩

private theorem k11t7_cover15 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 11 7 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p6, Certificates.k11t7p6_check⟩

private theorem k11t7_cover16 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 11 7 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p7, Certificates.k11t7p7_check⟩

private theorem k11t7_cover17 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 11 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover18 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 11 7 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p8, Certificates.k11t7p8_check⟩

private theorem k11t7_cover19 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 11 7 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover20 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 11 7 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover5 : ∀ P ∈ pathPatterns 3 4 [], HasCheckedCertificate 11 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover13
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t7_cover14
              · exact by
                  intro _
                  exact k11t7_cover15
              · exact by
                  intro _
                  exact k11t7_cover16
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover17
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k11t7_cover18
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover19
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover20
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover22 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 11 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p9, Certificates.k11t7p9_check⟩

private theorem k11t7_cover23 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 7 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p10, Certificates.k11t7p10_check⟩

private theorem k11t7_cover24 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 7 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p11, Certificates.k11t7p11_check⟩

private theorem k11t7_cover21 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 11 7 ([[], [], [], [1]] ++ P) := by
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
            exact k11t7_cover22
        · exact by
            intro _
            exact k11t7_cover23
        · exact by
            intro _
            exact k11t7_cover24

private theorem k11t7_cover25 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 11 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover26 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 11 7 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p12, Certificates.k11t7p12_check⟩

private theorem k11t7_cover27 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 11 7 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p13, Certificates.k11t7p13_check⟩

private theorem k11t7_cover28 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 11 7 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover29 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 11 7 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p14, Certificates.k11t7p14_check⟩

private theorem k11t7_cover30 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 11 7 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover32 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 7 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p15, Certificates.k11t7p15_check⟩

private theorem k11t7_cover31 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 11 7 ([[], [], [], [2]] ++ P) := by
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
            exact k11t7_cover32

private theorem k11t7_cover33 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 11 7 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover34 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 11 7 ([[], [], [], [3]] ++ P) := by
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

private theorem k11t7_cover35 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 11 7 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover4 : ∀ P ∈ pathPatterns 4 4 [], HasCheckedCertificate 11 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover21
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover25
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t7_cover26
                    · exact by
                        intro _
                        exact k11t7_cover27
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover28
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t7_cover29
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover30
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover31
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
                      exact k11t7_cover33
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover34
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
                exact k11t7_cover35
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover37 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 11 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover38 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 11 7 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p16, Certificates.k11t7p16_check⟩

private theorem k11t7_cover39 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 11 7 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p17, Certificates.k11t7p17_check⟩

private theorem k11t7_cover40 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 11 7 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover41 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 11 7 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover36 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 11 7 ([[], [], [1]] ++ P) := by
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
                exact k11t7_cover37
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t7_cover38
              · exact by
                  intro _
                  exact k11t7_cover39
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover40
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover41
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover43 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 7 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p18, Certificates.k11t7p18_check⟩

private theorem k11t7_cover42 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 11 7 ([[], [], [1, 1]] ++ P) := by
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
            exact k11t7_cover43

private theorem k11t7_cover44 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 11 7 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover45 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 11 7 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p19, Certificates.k11t7p19_check⟩

private theorem k11t7_cover46 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 11 7 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover47 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 11 7 ([[], [], [1, 2]] ++ P) := by
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

private theorem k11t7_cover48 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 11 7 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover49 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 11 7 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover51 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 11 7 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover50 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 11 7 ([[], [], [2]] ++ P) := by
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
                exact k11t7_cover51
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover52 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 11 7 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover53 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 11 7 ([[], [], [3]] ++ P) := by
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

private theorem k11t7_cover54 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 11 7 ([[], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover3 : ∀ P ∈ pathPatterns 5 4 [], HasCheckedCertificate 11 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover36
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover42
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover44
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k11t7_cover45
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover46
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover47
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover48
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover49
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover50
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
                      exact k11t7_cover52
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover53
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
                exact k11t7_cover54
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover57 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 11 7 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p20, Certificates.k11t7p20_check⟩

private theorem k11t7_cover58 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 7 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p21, Certificates.k11t7p21_check⟩

private theorem k11t7_cover56 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 11 7 ([[], [1], [1]] ++ P) := by
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
            exact k11t7_cover57
        · exact by
            intro _
            exact k11t7_cover58

private theorem k11t7_cover59 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 11 7 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover60 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 11 7 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p22, Certificates.k11t7p22_check⟩

private theorem k11t7_cover61 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 11 7 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover62 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 11 7 ([[], [1], [2]] ++ P) := by
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

private theorem k11t7_cover63 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 11 7 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover55 : ∀ P ∈ pathPatterns 4 3 [1], HasCheckedCertificate 11 7 ([[], [1]] ++ P) := by
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
                exact k11t7_cover56
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover59
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t7_cover60
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover61
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover62
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
                exact k11t7_cover63
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover65 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 11 7 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p23, Certificates.k11t7p23_check⟩

private theorem k11t7_cover66 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 11 7 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover64 : ∀ P ∈ pathPatterns 3 2 [1, 1], HasCheckedCertificate 11 7 ([[], [1, 1]] ++ P) := by
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
                  exact k11t7_cover65
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover66
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover67 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1], HasCheckedCertificate 11 7 ([[], [1, 1, 1]] ++ P) := by
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

private theorem k11t7_cover68 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1], HasCheckedCertificate 11 7 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover69 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2], HasCheckedCertificate 11 7 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover70 : ∀ P ∈ pathPatterns 3 1 [1, 2], HasCheckedCertificate 11 7 ([[], [1, 2]] ++ P) := by
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

private theorem k11t7_cover71 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1], HasCheckedCertificate 11 7 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover72 : ∀ P ∈ pathPatterns 3 0 [1, 3], HasCheckedCertificate 11 7 ([[], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover74 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 11 7 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover73 : ∀ P ∈ pathPatterns 4 2 [2], HasCheckedCertificate 11 7 ([[], [2]] ++ P) := by
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
                exact k11t7_cover74
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover75 : ∀ P ∈ pathPatterns 3 0 [2, 2], HasCheckedCertificate 11 7 ([[], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover76 : ∀ P ∈ pathPatterns 4 1 [3], HasCheckedCertificate 11 7 ([[], [3]] ++ P) := by
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

private theorem k11t7_cover77 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 11 7 ([[], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover2 : ∀ P ∈ pathPatterns 6 4 [], HasCheckedCertificate 11 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover55
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover64
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover67
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k11t7_cover68
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover69
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover70
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover71
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover72
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover73
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
                      exact k11t7_cover75
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover76
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
                exact k11t7_cover77
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover80 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 11 7 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover81 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 11 7 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t7p24, Certificates.k11t7p24_check⟩

private theorem k11t7_cover82 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 11 7 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover79 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 11 7 ([[1], [1]] ++ P) := by
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
                exact k11t7_cover80
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t7_cover81
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover82
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover83 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 11 7 ([[1], [1, 1]] ++ P) := by
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

private theorem k11t7_cover84 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 11 7 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover85 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 11 7 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover86 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 11 7 ([[1], [2]] ++ P) := by
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

private theorem k11t7_cover87 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 11 7 ([[1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover78 : ∀ P ∈ pathPatterns 5 3 [1], HasCheckedCertificate 11 7 ([[1]] ++ P) := by
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
                exact k11t7_cover79
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover83
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover84
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover85
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover86
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
                exact k11t7_cover87
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover89 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 11 7 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t7_cover90 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 11 7 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover88 : ∀ P ∈ pathPatterns 4 2 [1, 1], HasCheckedCertificate 11 7 ([[1, 1]] ++ P) := by
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
                      exact k11t7_cover89
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover90
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover91 : ∀ P ∈ pathPatterns 3 1 [1, 1, 1], HasCheckedCertificate 11 7 ([[1, 1, 1]] ++ P) := by
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

private theorem k11t7_cover92 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 1], HasCheckedCertificate 11 7 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover93 : ∀ P ∈ pathPatterns 3 0 [1, 1, 2], HasCheckedCertificate 11 7 ([[1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover94 : ∀ P ∈ pathPatterns 4 1 [1, 2], HasCheckedCertificate 11 7 ([[1, 2]] ++ P) := by
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

private theorem k11t7_cover95 : ∀ P ∈ pathPatterns 3 0 [1, 2, 1], HasCheckedCertificate 11 7 ([[1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover96 : ∀ P ∈ pathPatterns 4 0 [1, 3], HasCheckedCertificate 11 7 ([[1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover98 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 11 7 ([[2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover97 : ∀ P ∈ pathPatterns 5 2 [2], HasCheckedCertificate 11 7 ([[2]] ++ P) := by
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
                exact k11t7_cover98
            · intro q
              exact Fin.elim0 q

private theorem k11t7_cover99 : ∀ P ∈ pathPatterns 4 0 [2, 2], HasCheckedCertificate 11 7 ([[2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover100 : ∀ P ∈ pathPatterns 5 1 [3], HasCheckedCertificate 11 7 ([[3]] ++ P) := by
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

private theorem k11t7_cover101 : ∀ P ∈ pathPatterns 5 0 [4], HasCheckedCertificate 11 7 ([[4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t7_cover1 : ∀ P ∈ pathPatterns 7 4 [], HasCheckedCertificate 11 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t7_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover78
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover88
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover91
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k11t7_cover92
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover93
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover94
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t7_cover95
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t7_cover96
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover97
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
                      exact k11t7_cover99
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t7_cover100
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
                exact k11t7_cover101
            · intro q
              exact Fin.elim0 q

theorem coverage_k11_t7 :
    ∀ P ∈ pathPatterns 7 4, HasCheckedCertificate 11 7 P :=
  k11t7_cover1

private theorem k11t8_cover9 : ∀ P ∈ pathPatterns 0 3 [], HasCheckedCertificate 11 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p0, Certificates.k11t8p0_check⟩

private theorem k11t8_cover8 : ∀ P ∈ pathPatterns 1 3 [], HasCheckedCertificate 11 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k11t8_cover9

private theorem k11t8_cover10 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 11 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p1, Certificates.k11t8p1_check⟩

private theorem k11t8_cover11 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 11 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p2, Certificates.k11t8p2_check⟩

private theorem k11t8_cover12 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 11 8 ([[], [], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p3, Certificates.k11t8p3_check⟩

private theorem k11t8_cover7 : ∀ P ∈ pathPatterns 2 3 [], HasCheckedCertificate 11 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover8
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k11t8_cover10
        · exact by
            intro _
            exact k11t8_cover11
        · exact by
            intro _
            exact k11t8_cover12

private theorem k11t8_cover13 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 11 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover14 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 11 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p4, Certificates.k11t8p4_check⟩

private theorem k11t8_cover15 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 11 8 ([[], [], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p5, Certificates.k11t8p5_check⟩

private theorem k11t8_cover16 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 11 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover17 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 11 8 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover6 : ∀ P ∈ pathPatterns 3 3 [], HasCheckedCertificate 11 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover7
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover13
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t8_cover14
              · exact by
                  intro _
                  exact k11t8_cover15
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover16
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover17
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover19 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 11 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p6, Certificates.k11t8p6_check⟩

private theorem k11t8_cover20 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 11 8 ([[], [], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p7, Certificates.k11t8p7_check⟩

private theorem k11t8_cover18 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 11 8 ([[], [], [], [], [1]] ++ P) := by
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
            exact k11t8_cover19
        · exact by
            intro _
            exact k11t8_cover20

private theorem k11t8_cover21 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 11 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover22 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 11 8 ([[], [], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p8, Certificates.k11t8p8_check⟩

private theorem k11t8_cover23 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 11 8 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover24 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 11 8 ([[], [], [], [], [2]] ++ P) := by
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

private theorem k11t8_cover25 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 11 8 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover5 : ∀ P ∈ pathPatterns 4 3 [], HasCheckedCertificate 11 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover6
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover18
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover21
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k11t8_cover22
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover23
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover24
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
                exact k11t8_cover25
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover27 : ∀ P ∈ pathPatterns 1 1 [1], HasCheckedCertificate 11 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover28 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 11 8 ([[], [], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p9, Certificates.k11t8p9_check⟩

private theorem k11t8_cover29 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 11 8 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover26 : ∀ P ∈ pathPatterns 3 2 [1], HasCheckedCertificate 11 8 ([[], [], [], [1]] ++ P) := by
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
                exact k11t8_cover27
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k11t8_cover28
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover29
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover30 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 11 8 ([[], [], [], [1, 1]] ++ P) := by
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

private theorem k11t8_cover31 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 11 8 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover32 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 11 8 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover33 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 11 8 ([[], [], [], [2]] ++ P) := by
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

private theorem k11t8_cover34 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 11 8 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover4 : ∀ P ∈ pathPatterns 5 3 [], HasCheckedCertificate 11 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover5
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover26
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover30
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t8_cover31
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover32
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover33
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
                exact k11t8_cover34
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover37 : ∀ P ∈ pathPatterns 0 0 [1], HasCheckedCertificate 11 8 ([[], [], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k11t8p10, Certificates.k11t8p10_check⟩

private theorem k11t8_cover36 : ∀ P ∈ pathPatterns 2 1 [1], HasCheckedCertificate 11 8 ([[], [], [1], [1]] ++ P) := by
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
            exact k11t8_cover37

private theorem k11t8_cover38 : ∀ P ∈ pathPatterns 1 0 [1, 1], HasCheckedCertificate 11 8 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover39 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 11 8 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover35 : ∀ P ∈ pathPatterns 4 2 [1], HasCheckedCertificate 11 8 ([[], [], [1]] ++ P) := by
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
                exact k11t8_cover36
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover38
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover39
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover40 : ∀ P ∈ pathPatterns 3 1 [1, 1], HasCheckedCertificate 11 8 ([[], [], [1, 1]] ++ P) := by
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

private theorem k11t8_cover41 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1], HasCheckedCertificate 11 8 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover42 : ∀ P ∈ pathPatterns 3 0 [1, 2], HasCheckedCertificate 11 8 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover43 : ∀ P ∈ pathPatterns 4 1 [2], HasCheckedCertificate 11 8 ([[], [], [2]] ++ P) := by
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

private theorem k11t8_cover44 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 11 8 ([[], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover3 : ∀ P ∈ pathPatterns 6 3 [], HasCheckedCertificate 11 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover4
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover35
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover40
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t8_cover41
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover42
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover43
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
                exact k11t8_cover44
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover47 : ∀ P ∈ pathPatterns 1 0 [1], HasCheckedCertificate 11 8 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k11t8_cover46 : ∀ P ∈ pathPatterns 3 1 [1], HasCheckedCertificate 11 8 ([[], [1], [1]] ++ P) := by
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
                exact k11t8_cover47
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover48 : ∀ P ∈ pathPatterns 2 0 [1, 1], HasCheckedCertificate 11 8 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover49 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 11 8 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover45 : ∀ P ∈ pathPatterns 5 2 [1], HasCheckedCertificate 11 8 ([[], [1]] ++ P) := by
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
                exact k11t8_cover46
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover48
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover49
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover50 : ∀ P ∈ pathPatterns 4 1 [1, 1], HasCheckedCertificate 11 8 ([[], [1, 1]] ++ P) := by
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

private theorem k11t8_cover51 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1], HasCheckedCertificate 11 8 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover52 : ∀ P ∈ pathPatterns 4 0 [1, 2], HasCheckedCertificate 11 8 ([[], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover53 : ∀ P ∈ pathPatterns 5 1 [2], HasCheckedCertificate 11 8 ([[], [2]] ++ P) := by
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

private theorem k11t8_cover54 : ∀ P ∈ pathPatterns 5 0 [3], HasCheckedCertificate 11 8 ([[], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover2 : ∀ P ∈ pathPatterns 7 3 [], HasCheckedCertificate 11 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover3
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover45
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover50
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t8_cover51
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover52
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover53
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
                exact k11t8_cover54
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover57 : ∀ P ∈ pathPatterns 2 0 [1], HasCheckedCertificate 11 8 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover56 : ∀ P ∈ pathPatterns 4 1 [1], HasCheckedCertificate 11 8 ([[1], [1]] ++ P) := by
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
                exact k11t8_cover57
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover58 : ∀ P ∈ pathPatterns 3 0 [1, 1], HasCheckedCertificate 11 8 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover59 : ∀ P ∈ pathPatterns 4 0 [2], HasCheckedCertificate 11 8 ([[1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover55 : ∀ P ∈ pathPatterns 6 2 [1], HasCheckedCertificate 11 8 ([[1]] ++ P) := by
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
                exact k11t8_cover56
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover58
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover59
            · intro q
              exact Fin.elim0 q

private theorem k11t8_cover60 : ∀ P ∈ pathPatterns 5 1 [1, 1], HasCheckedCertificate 11 8 ([[1, 1]] ++ P) := by
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

private theorem k11t8_cover61 : ∀ P ∈ pathPatterns 4 0 [1, 1, 1], HasCheckedCertificate 11 8 ([[1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover62 : ∀ P ∈ pathPatterns 5 0 [1, 2], HasCheckedCertificate 11 8 ([[1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover63 : ∀ P ∈ pathPatterns 6 1 [2], HasCheckedCertificate 11 8 ([[2]] ++ P) := by
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

private theorem k11t8_cover64 : ∀ P ∈ pathPatterns 6 0 [3], HasCheckedCertificate 11 8 ([[3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k11t8_cover1 : ∀ P ∈ pathPatterns 8 3 [], HasCheckedCertificate 11 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k11t8_cover2
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover55
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover60
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k11t8_cover61
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k11t8_cover62
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k11t8_cover63
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
                exact k11t8_cover64
            · intro q
              exact Fin.elim0 q

theorem coverage_k11_t8 :
    ∀ P ∈ pathPatterns 8 3, HasCheckedCertificate 11 8 P :=
  k11t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
