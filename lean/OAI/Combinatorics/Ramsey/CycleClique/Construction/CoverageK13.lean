import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificatesK13
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateCoverage

namespace OAI

namespace CycleClique.Construction.CertifiedCoverage

private theorem k13t6_cover11 : ∀ P ∈ pathPatterns 0 7 [], HasCheckedCertificate 13 6 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p0, Certificates.k13t6p0_check⟩

private theorem k13t6_cover10 : ∀ P ∈ pathPatterns 1 7 [], HasCheckedCertificate 13 6 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k13t6_cover11

private theorem k13t6_cover12 : ∀ P ∈ pathPatterns 0 6 [1], HasCheckedCertificate 13 6 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p1, Certificates.k13t6p1_check⟩

private theorem k13t6_cover13 : ∀ P ∈ pathPatterns 0 5 [2], HasCheckedCertificate 13 6 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p2, Certificates.k13t6p2_check⟩

private theorem k13t6_cover14 : ∀ P ∈ pathPatterns 0 4 [3], HasCheckedCertificate 13 6 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p3, Certificates.k13t6p3_check⟩

private theorem k13t6_cover15 : ∀ P ∈ pathPatterns 0 3 [4], HasCheckedCertificate 13 6 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p4, Certificates.k13t6p4_check⟩

private theorem k13t6_cover16 : ∀ P ∈ pathPatterns 0 2 [5], HasCheckedCertificate 13 6 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p5, Certificates.k13t6p5_check⟩

private theorem k13t6_cover17 : ∀ P ∈ pathPatterns 0 1 [6], HasCheckedCertificate 13 6 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p6, Certificates.k13t6p6_check⟩

private theorem k13t6_cover18 : ∀ P ∈ pathPatterns 0 0 [7], HasCheckedCertificate 13 6 ([[], [], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p7, Certificates.k13t6p7_check⟩

private theorem k13t6_cover9 : ∀ P ∈ pathPatterns 2 7 [], HasCheckedCertificate 13 6 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k13t6_cover10
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k13t6_cover12
        · exact by
            intro _
            exact k13t6_cover13
        · exact by
            intro _
            exact k13t6_cover14
        · exact by
            intro _
            exact k13t6_cover15
        · exact by
            intro _
            exact k13t6_cover16
        · exact by
            intro _
            exact k13t6_cover17
        · exact by
            intro _
            exact k13t6_cover18

private theorem k13t6_cover19 : ∀ P ∈ pathPatterns 1 6 [1], HasCheckedCertificate 13 6 ([[], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover20 : ∀ P ∈ pathPatterns 0 5 [1, 1], HasCheckedCertificate 13 6 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p8, Certificates.k13t6p8_check⟩

private theorem k13t6_cover21 : ∀ P ∈ pathPatterns 0 4 [1, 2], HasCheckedCertificate 13 6 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p9, Certificates.k13t6p9_check⟩

private theorem k13t6_cover22 : ∀ P ∈ pathPatterns 0 3 [1, 3], HasCheckedCertificate 13 6 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p10, Certificates.k13t6p10_check⟩

private theorem k13t6_cover23 : ∀ P ∈ pathPatterns 0 2 [1, 4], HasCheckedCertificate 13 6 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p11, Certificates.k13t6p11_check⟩

private theorem k13t6_cover24 : ∀ P ∈ pathPatterns 0 1 [1, 5], HasCheckedCertificate 13 6 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p12, Certificates.k13t6p12_check⟩

private theorem k13t6_cover25 : ∀ P ∈ pathPatterns 0 0 [1, 6], HasCheckedCertificate 13 6 ([[], [], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p13, Certificates.k13t6p13_check⟩

private theorem k13t6_cover26 : ∀ P ∈ pathPatterns 1 5 [2], HasCheckedCertificate 13 6 ([[], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover27 : ∀ P ∈ pathPatterns 0 3 [2, 2], HasCheckedCertificate 13 6 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p14, Certificates.k13t6p14_check⟩

private theorem k13t6_cover28 : ∀ P ∈ pathPatterns 0 2 [2, 3], HasCheckedCertificate 13 6 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p15, Certificates.k13t6p15_check⟩

private theorem k13t6_cover29 : ∀ P ∈ pathPatterns 0 1 [2, 4], HasCheckedCertificate 13 6 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p16, Certificates.k13t6p16_check⟩

private theorem k13t6_cover30 : ∀ P ∈ pathPatterns 0 0 [2, 5], HasCheckedCertificate 13 6 ([[], [], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p17, Certificates.k13t6p17_check⟩

private theorem k13t6_cover31 : ∀ P ∈ pathPatterns 1 4 [3], HasCheckedCertificate 13 6 ([[], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover32 : ∀ P ∈ pathPatterns 0 1 [3, 3], HasCheckedCertificate 13 6 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p18, Certificates.k13t6p18_check⟩

private theorem k13t6_cover33 : ∀ P ∈ pathPatterns 0 0 [3, 4], HasCheckedCertificate 13 6 ([[], [], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p19, Certificates.k13t6p19_check⟩

private theorem k13t6_cover34 : ∀ P ∈ pathPatterns 1 3 [4], HasCheckedCertificate 13 6 ([[], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover35 : ∀ P ∈ pathPatterns 1 2 [5], HasCheckedCertificate 13 6 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover36 : ∀ P ∈ pathPatterns 1 1 [6], HasCheckedCertificate 13 6 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover37 : ∀ P ∈ pathPatterns 1 0 [7], HasCheckedCertificate 13 6 ([[], [], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)

private theorem k13t6_seq8 : amountSequenceForall 2 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (2 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover9
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover19
        · intro q
          fin_cases q
          · exact by
              intro _
              exact k13t6_cover20
          · exact by
              intro _
              exact k13t6_cover21
          · exact by
              intro _
              exact k13t6_cover22
          · exact by
              intro _
              exact k13t6_cover23
          · exact by
              intro _
              exact k13t6_cover24
          · exact by
              intro _
              exact k13t6_cover25
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover26
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
          · exact by
              intro _
              exact k13t6_cover27
          · exact by
              intro _
              exact k13t6_cover28
          · exact by
              intro _
              exact k13t6_cover29
          · exact by
              intro _
              exact k13t6_cover30
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover31
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
              exact k13t6_cover32
          · exact by
              intro _
              exact k13t6_cover33
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover34
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover35
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover36
        · intro q
          fin_cases q
          · exact by
              intro h
              exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover37
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover7 : ∀ P ∈ pathPatterns 3 7 [], HasCheckedCertificate 13 6 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq8


private theorem k13t6_cover39 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 13 6 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p20, Certificates.k13t6p20_check⟩

private theorem k13t6_cover40 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 13 6 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p21, Certificates.k13t6p21_check⟩

private theorem k13t6_cover41 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 13 6 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p22, Certificates.k13t6p22_check⟩

private theorem k13t6_cover42 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 13 6 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p23, Certificates.k13t6p23_check⟩

private theorem k13t6_cover43 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 13 6 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p24, Certificates.k13t6p24_check⟩

private theorem k13t6_cover44 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 13 6 ([[], [], [1], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p25, Certificates.k13t6p25_check⟩

private theorem k13t6_cover38 : ∀ P ∈ pathPatterns 2 6 [1], HasCheckedCertificate 13 6 ([[], [], [1]] ++ P) := by
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
            exact k13t6_cover39
        · exact by
            intro _
            exact k13t6_cover40
        · exact by
            intro _
            exact k13t6_cover41
        · exact by
            intro _
            exact k13t6_cover42
        · exact by
            intro _
            exact k13t6_cover43
        · exact by
            intro _
            exact k13t6_cover44

private theorem k13t6_cover45 : ∀ P ∈ pathPatterns 1 5 [1, 1], HasCheckedCertificate 13 6 ([[], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover46 : ∀ P ∈ pathPatterns 0 4 [1, 1, 1], HasCheckedCertificate 13 6 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p26, Certificates.k13t6p26_check⟩

private theorem k13t6_cover47 : ∀ P ∈ pathPatterns 0 3 [1, 1, 2], HasCheckedCertificate 13 6 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p27, Certificates.k13t6p27_check⟩

private theorem k13t6_cover48 : ∀ P ∈ pathPatterns 0 2 [1, 1, 3], HasCheckedCertificate 13 6 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p28, Certificates.k13t6p28_check⟩

private theorem k13t6_cover49 : ∀ P ∈ pathPatterns 0 1 [1, 1, 4], HasCheckedCertificate 13 6 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p29, Certificates.k13t6p29_check⟩

private theorem k13t6_cover50 : ∀ P ∈ pathPatterns 0 0 [1, 1, 5], HasCheckedCertificate 13 6 ([[], [], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p30, Certificates.k13t6p30_check⟩

private theorem k13t6_cover51 : ∀ P ∈ pathPatterns 1 4 [1, 2], HasCheckedCertificate 13 6 ([[], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover52 : ∀ P ∈ pathPatterns 0 3 [1, 2, 1], HasCheckedCertificate 13 6 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p31, Certificates.k13t6p31_check⟩

private theorem k13t6_cover53 : ∀ P ∈ pathPatterns 0 2 [1, 2, 2], HasCheckedCertificate 13 6 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p32, Certificates.k13t6p32_check⟩

private theorem k13t6_cover54 : ∀ P ∈ pathPatterns 0 1 [1, 2, 3], HasCheckedCertificate 13 6 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p33, Certificates.k13t6p33_check⟩

private theorem k13t6_cover55 : ∀ P ∈ pathPatterns 0 0 [1, 2, 4], HasCheckedCertificate 13 6 ([[], [], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p34, Certificates.k13t6p34_check⟩

private theorem k13t6_cover56 : ∀ P ∈ pathPatterns 1 3 [1, 3], HasCheckedCertificate 13 6 ([[], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover57 : ∀ P ∈ pathPatterns 0 2 [1, 3, 1], HasCheckedCertificate 13 6 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p35, Certificates.k13t6p35_check⟩

private theorem k13t6_cover58 : ∀ P ∈ pathPatterns 0 1 [1, 3, 2], HasCheckedCertificate 13 6 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p36, Certificates.k13t6p36_check⟩

private theorem k13t6_cover59 : ∀ P ∈ pathPatterns 0 0 [1, 3, 3], HasCheckedCertificate 13 6 ([[], [], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p37, Certificates.k13t6p37_check⟩

private theorem k13t6_cover60 : ∀ P ∈ pathPatterns 1 2 [1, 4], HasCheckedCertificate 13 6 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover61 : ∀ P ∈ pathPatterns 0 1 [1, 4, 1], HasCheckedCertificate 13 6 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p38, Certificates.k13t6p38_check⟩

private theorem k13t6_cover62 : ∀ P ∈ pathPatterns 0 0 [1, 4, 2], HasCheckedCertificate 13 6 ([[], [], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p39, Certificates.k13t6p39_check⟩

private theorem k13t6_cover63 : ∀ P ∈ pathPatterns 1 1 [1, 5], HasCheckedCertificate 13 6 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover64 : ∀ P ∈ pathPatterns 0 0 [1, 5, 1], HasCheckedCertificate 13 6 ([[], [], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p40, Certificates.k13t6p40_check⟩

private theorem k13t6_cover65 : ∀ P ∈ pathPatterns 1 0 [1, 6], HasCheckedCertificate 13 6 ([[], [], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover67 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 13 6 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p41, Certificates.k13t6p41_check⟩

private theorem k13t6_cover68 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 13 6 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p42, Certificates.k13t6p42_check⟩

private theorem k13t6_cover69 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 13 6 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p43, Certificates.k13t6p43_check⟩

private theorem k13t6_cover70 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 13 6 ([[], [], [2], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p44, Certificates.k13t6p44_check⟩

private theorem k13t6_cover66 : ∀ P ∈ pathPatterns 2 5 [2], HasCheckedCertificate 13 6 ([[], [], [2]] ++ P) := by
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
            exact k13t6_cover67
        · exact by
            intro _
            exact k13t6_cover68
        · exact by
            intro _
            exact k13t6_cover69
        · exact by
            intro _
            exact k13t6_cover70

private theorem k13t6_cover71 : ∀ P ∈ pathPatterns 0 2 [2, 1, 2], HasCheckedCertificate 13 6 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p45, Certificates.k13t6p45_check⟩

private theorem k13t6_cover72 : ∀ P ∈ pathPatterns 0 1 [2, 1, 3], HasCheckedCertificate 13 6 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p46, Certificates.k13t6p46_check⟩

private theorem k13t6_cover73 : ∀ P ∈ pathPatterns 0 0 [2, 1, 4], HasCheckedCertificate 13 6 ([[], [], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p47, Certificates.k13t6p47_check⟩

private theorem k13t6_cover74 : ∀ P ∈ pathPatterns 1 3 [2, 2], HasCheckedCertificate 13 6 ([[], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover75 : ∀ P ∈ pathPatterns 0 1 [2, 2, 2], HasCheckedCertificate 13 6 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p48, Certificates.k13t6p48_check⟩

private theorem k13t6_cover76 : ∀ P ∈ pathPatterns 0 0 [2, 2, 3], HasCheckedCertificate 13 6 ([[], [], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p49, Certificates.k13t6p49_check⟩

private theorem k13t6_cover77 : ∀ P ∈ pathPatterns 1 2 [2, 3], HasCheckedCertificate 13 6 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover78 : ∀ P ∈ pathPatterns 0 0 [2, 3, 2], HasCheckedCertificate 13 6 ([[], [], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p50, Certificates.k13t6p50_check⟩

private theorem k13t6_cover79 : ∀ P ∈ pathPatterns 1 1 [2, 4], HasCheckedCertificate 13 6 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover80 : ∀ P ∈ pathPatterns 1 0 [2, 5], HasCheckedCertificate 13 6 ([[], [], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover82 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 6 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p51, Certificates.k13t6p51_check⟩

private theorem k13t6_cover83 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 6 ([[], [], [3], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p52, Certificates.k13t6p52_check⟩

private theorem k13t6_cover81 : ∀ P ∈ pathPatterns 2 4 [3], HasCheckedCertificate 13 6 ([[], [], [3]] ++ P) := by
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
            exact k13t6_cover82
        · exact by
            intro _
            exact k13t6_cover83

private theorem k13t6_cover84 : ∀ P ∈ pathPatterns 0 0 [3, 1, 3], HasCheckedCertificate 13 6 ([[], [], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p53, Certificates.k13t6p53_check⟩

private theorem k13t6_cover85 : ∀ P ∈ pathPatterns 1 1 [3, 3], HasCheckedCertificate 13 6 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover86 : ∀ P ∈ pathPatterns 1 0 [3, 4], HasCheckedCertificate 13 6 ([[], [], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover87 : ∀ P ∈ pathPatterns 2 3 [4], HasCheckedCertificate 13 6 ([[], [], [4]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)

private theorem k13t6_cover88 : ∀ P ∈ pathPatterns 2 2 [5], HasCheckedCertificate 13 6 ([[], [], [5]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)

private theorem k13t6_cover89 : ∀ P ∈ pathPatterns 2 1 [6], HasCheckedCertificate 13 6 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover90 : ∀ P ∈ pathPatterns 2 0 [7], HasCheckedCertificate 13 6 ([[], [], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq6 : amountSequenceForall 3 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover7
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover38
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover45
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover46
                · exact by
                    intro _
                    exact k13t6_cover47
                · exact by
                    intro _
                    exact k13t6_cover48
                · exact by
                    intro _
                    exact k13t6_cover49
                · exact by
                    intro _
                    exact k13t6_cover50
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover51
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover52
                · exact by
                    intro _
                    exact k13t6_cover53
                · exact by
                    intro _
                    exact k13t6_cover54
                · exact by
                    intro _
                    exact k13t6_cover55
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover56
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover57
                · exact by
                    intro _
                    exact k13t6_cover58
                · exact by
                    intro _
                    exact k13t6_cover59
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover60
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover61
                · exact by
                    intro _
                    exact k13t6_cover62
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover63
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover64
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover65
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover66
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
                    exact k13t6_cover71
                · exact by
                    intro _
                    exact k13t6_cover72
                · exact by
                    intro _
                    exact k13t6_cover73
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover74
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k13t6_cover75
                · exact by
                    intro _
                    exact k13t6_cover76
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover77
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
                · exact by
                    intro _
                    exact k13t6_cover78
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover79
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover80
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover81
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
                    intro _
                    exact k13t6_cover84
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover85
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover86
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover87
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover88
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover89
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover90
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover5 : ∀ P ∈ pathPatterns 4 7 [], HasCheckedCertificate 13 6 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq6


private theorem k13t6_cover93 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 13 6 ([[], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover94 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 13 6 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p54, Certificates.k13t6p54_check⟩

private theorem k13t6_cover95 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 13 6 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p55, Certificates.k13t6p55_check⟩

private theorem k13t6_cover96 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 13 6 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p56, Certificates.k13t6p56_check⟩

private theorem k13t6_cover97 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 13 6 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p57, Certificates.k13t6p57_check⟩

private theorem k13t6_cover98 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 13 6 ([[], [1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p58, Certificates.k13t6p58_check⟩

private theorem k13t6_cover99 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 13 6 ([[], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover100 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 13 6 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p59, Certificates.k13t6p59_check⟩

private theorem k13t6_cover101 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 13 6 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p60, Certificates.k13t6p60_check⟩

private theorem k13t6_cover102 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 13 6 ([[], [1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p61, Certificates.k13t6p61_check⟩

private theorem k13t6_cover103 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 13 6 ([[], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover104 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 13 6 ([[], [1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p62, Certificates.k13t6p62_check⟩

private theorem k13t6_cover105 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 13 6 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover106 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 13 6 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover107 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 13 6 ([[], [1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover92 : ∀ P ∈ pathPatterns 3 6 [1], HasCheckedCertificate 13 6 ([[], [1]] ++ P) := by
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
                exact k13t6_cover93
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t6_cover94
              · exact by
                  intro _
                  exact k13t6_cover95
              · exact by
                  intro _
                  exact k13t6_cover96
              · exact by
                  intro _
                  exact k13t6_cover97
              · exact by
                  intro _
                  exact k13t6_cover98
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover99
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t6_cover100
              · exact by
                  intro _
                  exact k13t6_cover101
              · exact by
                  intro _
                  exact k13t6_cover102
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover103
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · exact by
                  intro _
                  exact k13t6_cover104
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover105
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover106
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover107
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover109 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 13 6 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p63, Certificates.k13t6p63_check⟩

private theorem k13t6_cover110 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 13 6 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p64, Certificates.k13t6p64_check⟩

private theorem k13t6_cover111 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 13 6 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p65, Certificates.k13t6p65_check⟩

private theorem k13t6_cover112 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 13 6 ([[], [1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p66, Certificates.k13t6p66_check⟩

private theorem k13t6_cover108 : ∀ P ∈ pathPatterns 2 5 [1, 1], HasCheckedCertificate 13 6 ([[], [1, 1]] ++ P) := by
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
            exact k13t6_cover109
        · exact by
            intro _
            exact k13t6_cover110
        · exact by
            intro _
            exact k13t6_cover111
        · exact by
            intro _
            exact k13t6_cover112

private theorem k13t6_cover113 : ∀ P ∈ pathPatterns 1 4 [1, 1, 1], HasCheckedCertificate 13 6 ([[], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover114 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1, 1], HasCheckedCertificate 13 6 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p67, Certificates.k13t6p67_check⟩

private theorem k13t6_cover115 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 2], HasCheckedCertificate 13 6 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p68, Certificates.k13t6p68_check⟩

private theorem k13t6_cover116 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 3], HasCheckedCertificate 13 6 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p69, Certificates.k13t6p69_check⟩

private theorem k13t6_cover117 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 4], HasCheckedCertificate 13 6 ([[], [1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p70, Certificates.k13t6p70_check⟩

private theorem k13t6_cover118 : ∀ P ∈ pathPatterns 1 3 [1, 1, 2], HasCheckedCertificate 13 6 ([[], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover119 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2, 1], HasCheckedCertificate 13 6 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p71, Certificates.k13t6p71_check⟩

private theorem k13t6_cover120 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 2], HasCheckedCertificate 13 6 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p72, Certificates.k13t6p72_check⟩

private theorem k13t6_cover121 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 3], HasCheckedCertificate 13 6 ([[], [1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p73, Certificates.k13t6p73_check⟩

private theorem k13t6_cover122 : ∀ P ∈ pathPatterns 1 2 [1, 1, 3], HasCheckedCertificate 13 6 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover123 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3, 1], HasCheckedCertificate 13 6 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p74, Certificates.k13t6p74_check⟩

private theorem k13t6_cover124 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 2], HasCheckedCertificate 13 6 ([[], [1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p75, Certificates.k13t6p75_check⟩

private theorem k13t6_cover125 : ∀ P ∈ pathPatterns 1 1 [1, 1, 4], HasCheckedCertificate 13 6 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover126 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4, 1], HasCheckedCertificate 13 6 ([[], [1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p76, Certificates.k13t6p76_check⟩

private theorem k13t6_cover127 : ∀ P ∈ pathPatterns 1 0 [1, 1, 5], HasCheckedCertificate 13 6 ([[], [1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover129 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 6 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p77, Certificates.k13t6p77_check⟩

private theorem k13t6_cover130 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 6 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p78, Certificates.k13t6p78_check⟩

private theorem k13t6_cover131 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 6 ([[], [1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p79, Certificates.k13t6p79_check⟩

private theorem k13t6_cover128 : ∀ P ∈ pathPatterns 2 4 [1, 2], HasCheckedCertificate 13 6 ([[], [1, 2]] ++ P) := by
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
            exact k13t6_cover129
        · exact by
            intro _
            exact k13t6_cover130
        · exact by
            intro _
            exact k13t6_cover131

private theorem k13t6_cover132 : ∀ P ∈ pathPatterns 1 3 [1, 2, 1], HasCheckedCertificate 13 6 ([[], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover133 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1, 2], HasCheckedCertificate 13 6 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p80, Certificates.k13t6p80_check⟩

private theorem k13t6_cover134 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 3], HasCheckedCertificate 13 6 ([[], [1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p81, Certificates.k13t6p81_check⟩

private theorem k13t6_cover135 : ∀ P ∈ pathPatterns 1 2 [1, 2, 2], HasCheckedCertificate 13 6 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover136 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2, 1], HasCheckedCertificate 13 6 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p82, Certificates.k13t6p82_check⟩

private theorem k13t6_cover137 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 2], HasCheckedCertificate 13 6 ([[], [1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p83, Certificates.k13t6p83_check⟩

private theorem k13t6_cover138 : ∀ P ∈ pathPatterns 1 1 [1, 2, 3], HasCheckedCertificate 13 6 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover139 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3, 1], HasCheckedCertificate 13 6 ([[], [1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p84, Certificates.k13t6p84_check⟩

private theorem k13t6_cover140 : ∀ P ∈ pathPatterns 1 0 [1, 2, 4], HasCheckedCertificate 13 6 ([[], [1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover142 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 6 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p85, Certificates.k13t6p85_check⟩

private theorem k13t6_cover143 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[], [1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p86, Certificates.k13t6p86_check⟩

private theorem k13t6_cover141 : ∀ P ∈ pathPatterns 2 3 [1, 3], HasCheckedCertificate 13 6 ([[], [1, 3]] ++ P) := by
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
            exact k13t6_cover142
        · exact by
            intro _
            exact k13t6_cover143

private theorem k13t6_cover144 : ∀ P ∈ pathPatterns 1 2 [1, 3, 1], HasCheckedCertificate 13 6 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover145 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1, 2], HasCheckedCertificate 13 6 ([[], [1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p87, Certificates.k13t6p87_check⟩

private theorem k13t6_cover146 : ∀ P ∈ pathPatterns 1 1 [1, 3, 2], HasCheckedCertificate 13 6 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover147 : ∀ P ∈ pathPatterns 1 0 [1, 3, 3], HasCheckedCertificate 13 6 ([[], [1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover149 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 6 ([[], [1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p88, Certificates.k13t6p88_check⟩

private theorem k13t6_cover148 : ∀ P ∈ pathPatterns 2 2 [1, 4], HasCheckedCertificate 13 6 ([[], [1, 4]] ++ P) := by
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
        · exact by
            intro _
            exact k13t6_cover149

private theorem k13t6_cover150 : ∀ P ∈ pathPatterns 1 1 [1, 4, 1], HasCheckedCertificate 13 6 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover151 : ∀ P ∈ pathPatterns 1 0 [1, 4, 2], HasCheckedCertificate 13 6 ([[], [1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover152 : ∀ P ∈ pathPatterns 2 1 [1, 5], HasCheckedCertificate 13 6 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover153 : ∀ P ∈ pathPatterns 1 0 [1, 5, 1], HasCheckedCertificate 13 6 ([[], [1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover154 : ∀ P ∈ pathPatterns 2 0 [1, 6], HasCheckedCertificate 13 6 ([[], [1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq91 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 13 6 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover92
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover108
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover113
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover114
                · exact by
                    intro _
                    exact k13t6_cover115
                · exact by
                    intro _
                    exact k13t6_cover116
                · exact by
                    intro _
                    exact k13t6_cover117
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover118
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover119
                · exact by
                    intro _
                    exact k13t6_cover120
                · exact by
                    intro _
                    exact k13t6_cover121
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover122
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover123
                · exact by
                    intro _
                    exact k13t6_cover124
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover125
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover126
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover127
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover128
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover132
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k13t6_cover133
                · exact by
                    intro _
                    exact k13t6_cover134
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover135
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover136
                · exact by
                    intro _
                    exact k13t6_cover137
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover138
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover139
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover140
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover141
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover144
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                · exact by
                    intro _
                    exact k13t6_cover145
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover146
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover147
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover148
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover150
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover151
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover152
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover153
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover154
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover157 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 13 6 ([[], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover158 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 13 6 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p89, Certificates.k13t6p89_check⟩

private theorem k13t6_cover159 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 13 6 ([[], [2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p90, Certificates.k13t6p90_check⟩

private theorem k13t6_cover160 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 13 6 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover161 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 13 6 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover162 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 13 6 ([[], [2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover156 : ∀ P ∈ pathPatterns 3 5 [2], HasCheckedCertificate 13 6 ([[], [2]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover157
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t6_cover158
              · exact by
                  intro _
                  exact k13t6_cover159
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover160
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover161
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover162
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover163 : ∀ P ∈ pathPatterns 0 1 [2, 1, 1, 2], HasCheckedCertificate 13 6 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p91, Certificates.k13t6p91_check⟩

private theorem k13t6_cover164 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 3], HasCheckedCertificate 13 6 ([[], [2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p92, Certificates.k13t6p92_check⟩

private theorem k13t6_cover165 : ∀ P ∈ pathPatterns 1 2 [2, 1, 2], HasCheckedCertificate 13 6 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover166 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2, 2], HasCheckedCertificate 13 6 ([[], [2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p93, Certificates.k13t6p93_check⟩

private theorem k13t6_cover167 : ∀ P ∈ pathPatterns 1 1 [2, 1, 3], HasCheckedCertificate 13 6 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover168 : ∀ P ∈ pathPatterns 1 0 [2, 1, 4], HasCheckedCertificate 13 6 ([[], [2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover170 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[], [2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p94, Certificates.k13t6p94_check⟩

private theorem k13t6_cover169 : ∀ P ∈ pathPatterns 2 3 [2, 2], HasCheckedCertificate 13 6 ([[], [2, 2]] ++ P) := by
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
        · exact by
            intro _
            exact k13t6_cover170

private theorem k13t6_cover171 : ∀ P ∈ pathPatterns 1 1 [2, 2, 2], HasCheckedCertificate 13 6 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover172 : ∀ P ∈ pathPatterns 1 0 [2, 2, 3], HasCheckedCertificate 13 6 ([[], [2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover173 : ∀ P ∈ pathPatterns 2 2 [2, 3], HasCheckedCertificate 13 6 ([[], [2, 3]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)

private theorem k13t6_cover174 : ∀ P ∈ pathPatterns 1 0 [2, 3, 2], HasCheckedCertificate 13 6 ([[], [2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover175 : ∀ P ∈ pathPatterns 2 1 [2, 4], HasCheckedCertificate 13 6 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover176 : ∀ P ∈ pathPatterns 2 0 [2, 5], HasCheckedCertificate 13 6 ([[], [2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq155 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 13 6 ([[]] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover156
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
                    exact k13t6_cover163
                · exact by
                    intro _
                    exact k13t6_cover164
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover165
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    intro _
                    exact k13t6_cover166
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover167
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover168
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover169
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover171
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover172
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover173
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover174
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover175
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover176
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover178 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 6 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover179 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 6 ([[], [3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover177 : ∀ P ∈ pathPatterns 3 4 [3], HasCheckedCertificate 13 6 ([[], [3]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover178
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover179
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover180 : ∀ P ∈ pathPatterns 1 0 [3, 1, 3], HasCheckedCertificate 13 6 ([[], [3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover181 : ∀ P ∈ pathPatterns 2 1 [3, 3], HasCheckedCertificate 13 6 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover182 : ∀ P ∈ pathPatterns 2 0 [3, 4], HasCheckedCertificate 13 6 ([[], [3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover183 : ∀ P ∈ pathPatterns 3 3 [4], HasCheckedCertificate 13 6 ([[], [4]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover184 : ∀ P ∈ pathPatterns 3 2 [5], HasCheckedCertificate 13 6 ([[], [5]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover185 : ∀ P ∈ pathPatterns 3 1 [6], HasCheckedCertificate 13 6 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover186 : ∀ P ∈ pathPatterns 3 0 [7], HasCheckedCertificate 13 6 ([[], [7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq4 : amountSequenceForall 4 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover5
  · intro q
    fin_cases q
    · exact k13t6_seq91

    · exact k13t6_seq155

    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover177
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
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover180
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover181
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover182
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover183
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover184
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover185
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover186
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover3 : ∀ P ∈ pathPatterns 5 7 [], HasCheckedCertificate 13 6 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq4


private theorem k13t6_cover191 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 13 6 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p95, Certificates.k13t6p95_check⟩

private theorem k13t6_cover192 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 13 6 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p96, Certificates.k13t6p96_check⟩

private theorem k13t6_cover193 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 13 6 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p97, Certificates.k13t6p97_check⟩

private theorem k13t6_cover194 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 13 6 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p98, Certificates.k13t6p98_check⟩

private theorem k13t6_cover195 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 13 6 ([[1], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p99, Certificates.k13t6p99_check⟩

private theorem k13t6_cover190 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 13 6 ([[1], [1]] ++ P) := by
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
            exact k13t6_cover191
        · exact by
            intro _
            exact k13t6_cover192
        · exact by
            intro _
            exact k13t6_cover193
        · exact by
            intro _
            exact k13t6_cover194
        · exact by
            intro _
            exact k13t6_cover195

private theorem k13t6_cover196 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 13 6 ([[1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover197 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 13 6 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p100, Certificates.k13t6p100_check⟩

private theorem k13t6_cover198 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 13 6 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p101, Certificates.k13t6p101_check⟩

private theorem k13t6_cover199 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 13 6 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p102, Certificates.k13t6p102_check⟩

private theorem k13t6_cover200 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 13 6 ([[1], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p103, Certificates.k13t6p103_check⟩

private theorem k13t6_cover201 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 13 6 ([[1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover202 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 13 6 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p104, Certificates.k13t6p104_check⟩

private theorem k13t6_cover203 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 13 6 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p105, Certificates.k13t6p105_check⟩

private theorem k13t6_cover204 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 13 6 ([[1], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p106, Certificates.k13t6p106_check⟩

private theorem k13t6_cover205 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 13 6 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover206 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 13 6 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p107, Certificates.k13t6p107_check⟩

private theorem k13t6_cover207 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 13 6 ([[1], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p108, Certificates.k13t6p108_check⟩

private theorem k13t6_cover208 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 13 6 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover209 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 13 6 ([[1], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p109, Certificates.k13t6p109_check⟩

private theorem k13t6_cover210 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 13 6 ([[1], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover212 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 6 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p110, Certificates.k13t6p110_check⟩

private theorem k13t6_cover213 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 6 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p111, Certificates.k13t6p111_check⟩

private theorem k13t6_cover214 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 6 ([[1], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p112, Certificates.k13t6p112_check⟩

private theorem k13t6_cover211 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 13 6 ([[1], [2]] ++ P) := by
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
            exact k13t6_cover212
        · exact by
            intro _
            exact k13t6_cover213
        · exact by
            intro _
            exact k13t6_cover214

private theorem k13t6_cover215 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 13 6 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p113, Certificates.k13t6p113_check⟩

private theorem k13t6_cover216 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 13 6 ([[1], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p114, Certificates.k13t6p114_check⟩

private theorem k13t6_cover217 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 13 6 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover218 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 13 6 ([[1], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p115, Certificates.k13t6p115_check⟩

private theorem k13t6_cover219 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 13 6 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover220 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 13 6 ([[1], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover222 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[1], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p116, Certificates.k13t6p116_check⟩

private theorem k13t6_cover221 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 13 6 ([[1], [3]] ++ P) := by
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
            exact k13t6_cover222

private theorem k13t6_cover223 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 13 6 ([[1], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover224 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 13 6 ([[1], [4]] ++ P) := by
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

private theorem k13t6_cover225 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 13 6 ([[1], [5]] ++ P) := by
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

private theorem k13t6_cover226 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 13 6 ([[1], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq189 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([[1]] ++ (([] ++ tail) :: P))) :=
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
            exact k13t6_cover190
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover196
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover197
                · exact by
                    intro _
                    exact k13t6_cover198
                · exact by
                    intro _
                    exact k13t6_cover199
                · exact by
                    intro _
                    exact k13t6_cover200
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover201
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover202
                · exact by
                    intro _
                    exact k13t6_cover203
                · exact by
                    intro _
                    exact k13t6_cover204
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover205
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover206
                · exact by
                    intro _
                    exact k13t6_cover207
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover208
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover209
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover210
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover211
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
                    exact k13t6_cover215
                · exact by
                    intro _
                    exact k13t6_cover216
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover217
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k13t6_cover218
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover219
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover220
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover221
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [3, 2, 1] ∧ LexLE [3, 2, 1] [1, 2, 3])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover223
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover224
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [4, 1, 1] ∧ LexLE [4, 1, 1] [1, 1, 4])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover225
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover226
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover188 : ∀ P ∈ pathPatterns 4 6 [1], HasCheckedCertificate 13 6 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq189


private theorem k13t6_cover229 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 13 6 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p117, Certificates.k13t6p117_check⟩

private theorem k13t6_cover230 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 13 6 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p118, Certificates.k13t6p118_check⟩

private theorem k13t6_cover231 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 13 6 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p119, Certificates.k13t6p119_check⟩

private theorem k13t6_cover232 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 13 6 ([[1, 1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p120, Certificates.k13t6p120_check⟩

private theorem k13t6_cover233 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 13 6 ([[1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover234 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 13 6 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p121, Certificates.k13t6p121_check⟩

private theorem k13t6_cover235 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 13 6 ([[1, 1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p122, Certificates.k13t6p122_check⟩

private theorem k13t6_cover236 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 13 6 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover237 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 13 6 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover238 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 13 6 ([[1, 1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover228 : ∀ P ∈ pathPatterns 3 5 [1, 1], HasCheckedCertificate 13 6 ([[1, 1]] ++ P) := by
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
                  exact k13t6_cover229
              · exact by
                  intro _
                  exact k13t6_cover230
              · exact by
                  intro _
                  exact k13t6_cover231
              · exact by
                  intro _
                  exact k13t6_cover232
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover233
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t6_cover234
              · exact by
                  intro _
                  exact k13t6_cover235
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover236
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover237
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover238
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover240 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 6 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p123, Certificates.k13t6p123_check⟩

private theorem k13t6_cover241 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 6 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p124, Certificates.k13t6p124_check⟩

private theorem k13t6_cover242 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 6 ([[1, 1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p125, Certificates.k13t6p125_check⟩

private theorem k13t6_cover239 : ∀ P ∈ pathPatterns 2 4 [1, 1, 1], HasCheckedCertificate 13 6 ([[1, 1, 1]] ++ P) := by
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
            exact k13t6_cover240
        · exact by
            intro _
            exact k13t6_cover241
        · exact by
            intro _
            exact k13t6_cover242

private theorem k13t6_cover243 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1, 1], HasCheckedCertificate 13 6 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover244 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1, 1], HasCheckedCertificate 13 6 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p126, Certificates.k13t6p126_check⟩

private theorem k13t6_cover245 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 2], HasCheckedCertificate 13 6 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p127, Certificates.k13t6p127_check⟩

private theorem k13t6_cover246 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 3], HasCheckedCertificate 13 6 ([[1, 1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p128, Certificates.k13t6p128_check⟩

private theorem k13t6_cover247 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 2], HasCheckedCertificate 13 6 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover248 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2, 1], HasCheckedCertificate 13 6 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p129, Certificates.k13t6p129_check⟩

private theorem k13t6_cover249 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 2], HasCheckedCertificate 13 6 ([[1, 1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p130, Certificates.k13t6p130_check⟩

private theorem k13t6_cover250 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 3], HasCheckedCertificate 13 6 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover251 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3, 1], HasCheckedCertificate 13 6 ([[1, 1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p131, Certificates.k13t6p131_check⟩

private theorem k13t6_cover252 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 4], HasCheckedCertificate 13 6 ([[1, 1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover254 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 6 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p132, Certificates.k13t6p132_check⟩

private theorem k13t6_cover255 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[1, 1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p133, Certificates.k13t6p133_check⟩

private theorem k13t6_cover253 : ∀ P ∈ pathPatterns 2 3 [1, 1, 2], HasCheckedCertificate 13 6 ([[1, 1, 2]] ++ P) := by
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
            exact k13t6_cover254
        · exact by
            intro _
            exact k13t6_cover255

private theorem k13t6_cover256 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2, 1], HasCheckedCertificate 13 6 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover257 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1, 1], HasCheckedCertificate 13 6 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p134, Certificates.k13t6p134_check⟩

private theorem k13t6_cover258 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 2], HasCheckedCertificate 13 6 ([[1, 1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p135, Certificates.k13t6p135_check⟩

private theorem k13t6_cover259 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 2], HasCheckedCertificate 13 6 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover260 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2, 1], HasCheckedCertificate 13 6 ([[1, 1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p136, Certificates.k13t6p136_check⟩

private theorem k13t6_cover261 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 3], HasCheckedCertificate 13 6 ([[1, 1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover263 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 6 ([[1, 1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p137, Certificates.k13t6p137_check⟩

private theorem k13t6_cover262 : ∀ P ∈ pathPatterns 2 2 [1, 1, 3], HasCheckedCertificate 13 6 ([[1, 1, 3]] ++ P) := by
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
        · exact by
            intro _
            exact k13t6_cover263

private theorem k13t6_cover264 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3, 1], HasCheckedCertificate 13 6 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover265 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1, 1], HasCheckedCertificate 13 6 ([[1, 1, 3, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p138, Certificates.k13t6p138_check⟩

private theorem k13t6_cover266 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 2], HasCheckedCertificate 13 6 ([[1, 1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover267 : ∀ P ∈ pathPatterns 2 1 [1, 1, 4], HasCheckedCertificate 13 6 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover268 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4, 1], HasCheckedCertificate 13 6 ([[1, 1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover269 : ∀ P ∈ pathPatterns 2 0 [1, 1, 5], HasCheckedCertificate 13 6 ([[1, 1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq227 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1, 1] ++ tail) ∧ LexLE ([1, 1] ++ tail) ([1, 1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1, 1] ++ tail).length) (7 - ([1, 1] ++ tail).sum) ([1, 1] ++ tail),
      HasCheckedCertificate 13 6 ([] ++ (([1, 1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover228
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover239
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover243
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover244
                · exact by
                    intro _
                    exact k13t6_cover245
                · exact by
                    intro _
                    exact k13t6_cover246
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover247
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover248
                · exact by
                    intro _
                    exact k13t6_cover249
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover250
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover251
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover252
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover253
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover256
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover257
                · exact by
                    intro _
                    exact k13t6_cover258
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover259
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover260
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover261
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover262
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover264
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t6_cover265
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover266
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover267
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover268
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover269
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover271 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 13 6 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p139, Certificates.k13t6p139_check⟩

private theorem k13t6_cover272 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 13 6 ([[1, 2], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p140, Certificates.k13t6p140_check⟩

private theorem k13t6_cover273 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 13 6 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover274 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 13 6 ([[1, 2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p141, Certificates.k13t6p141_check⟩

private theorem k13t6_cover275 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 6 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover276 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 6 ([[1, 2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover270 : ∀ P ∈ pathPatterns 3 4 [1, 2], HasCheckedCertificate 13 6 ([[1, 2]] ++ P) := by
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
                  exact k13t6_cover271
              · exact by
                  intro _
                  exact k13t6_cover272
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover273
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t6_cover274
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover275
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover276
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover278 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 6 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p142, Certificates.k13t6p142_check⟩

private theorem k13t6_cover279 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[1, 2, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p143, Certificates.k13t6p143_check⟩

private theorem k13t6_cover277 : ∀ P ∈ pathPatterns 2 3 [1, 2, 1], HasCheckedCertificate 13 6 ([[1, 2, 1]] ++ P) := by
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
            exact k13t6_cover278
        · exact by
            intro _
            exact k13t6_cover279

private theorem k13t6_cover280 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 1, 2], HasCheckedCertificate 13 6 ([[1, 2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p144, Certificates.k13t6p144_check⟩

private theorem k13t6_cover281 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1, 2], HasCheckedCertificate 13 6 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover282 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2, 1], HasCheckedCertificate 13 6 ([[1, 2, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p145, Certificates.k13t6p145_check⟩

private theorem k13t6_cover283 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 3], HasCheckedCertificate 13 6 ([[1, 2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover285 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 6 ([[1, 2, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p146, Certificates.k13t6p146_check⟩

private theorem k13t6_cover284 : ∀ P ∈ pathPatterns 2 2 [1, 2, 2], HasCheckedCertificate 13 6 ([[1, 2, 2]] ++ P) := by
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
        · exact by
            intro _
            exact k13t6_cover285

private theorem k13t6_cover286 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2, 1], HasCheckedCertificate 13 6 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover287 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 2], HasCheckedCertificate 13 6 ([[1, 2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover288 : ∀ P ∈ pathPatterns 2 1 [1, 2, 3], HasCheckedCertificate 13 6 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover289 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3, 1], HasCheckedCertificate 13 6 ([[1, 2, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover290 : ∀ P ∈ pathPatterns 2 0 [1, 2, 4], HasCheckedCertificate 13 6 ([[1, 2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover292 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 6 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover293 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 6 ([[1, 3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover291 : ∀ P ∈ pathPatterns 3 3 [1, 3], HasCheckedCertificate 13 6 ([[1, 3]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover292
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 3] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover293
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover295 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 6 ([[1, 3, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p147, Certificates.k13t6p147_check⟩

private theorem k13t6_cover294 : ∀ P ∈ pathPatterns 2 2 [1, 3, 1], HasCheckedCertificate 13 6 ([[1, 3, 1]] ++ P) := by
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
        · exact by
            intro _
            exact k13t6_cover295

private theorem k13t6_cover296 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1, 2], HasCheckedCertificate 13 6 ([[1, 3, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover297 : ∀ P ∈ pathPatterns 2 1 [1, 3, 2], HasCheckedCertificate 13 6 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover298 : ∀ P ∈ pathPatterns 2 0 [1, 3, 3], HasCheckedCertificate 13 6 ([[1, 3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover300 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 6 ([[1, 4], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover299 : ∀ P ∈ pathPatterns 3 2 [1, 4], HasCheckedCertificate 13 6 ([[1, 4]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 4] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover300
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover301 : ∀ P ∈ pathPatterns 2 1 [1, 4, 1], HasCheckedCertificate 13 6 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover302 : ∀ P ∈ pathPatterns 2 0 [1, 4, 2], HasCheckedCertificate 13 6 ([[1, 4, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover303 : ∀ P ∈ pathPatterns 3 1 [1, 5], HasCheckedCertificate 13 6 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 5] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover304 : ∀ P ∈ pathPatterns 2 0 [1, 5, 1], HasCheckedCertificate 13 6 ([[1, 5, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover305 : ∀ P ∈ pathPatterns 3 0 [1, 6], HasCheckedCertificate 13 6 ([[1, 6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq187 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (7 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 13 6 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover188
  · intro q
    fin_cases q
    · exact k13t6_seq227

    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover270
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover277
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
                          intro _
                          exact k13t6_cover280
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover281
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t6_cover282
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover283
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover284
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover286
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 2, 1, 1] ∧ LexLE [1, 2, 2, 1, 1] [1, 1, 2, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover287
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover288
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover289
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover290
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover291
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover294
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1, 1] ∧ LexLE [1, 3, 1, 1, 1] [1, 1, 1, 3, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover296
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover297
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 2, 1] ∧ LexLE [1, 3, 2, 1] [1, 2, 3, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover298
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover299
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover301
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [1, 4, 1, 1] ∧ LexLE [1, 4, 1, 1] [1, 1, 4, 1])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover302
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover303
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover304
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover305
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover310 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 6 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p148, Certificates.k13t6p148_check⟩

private theorem k13t6_cover311 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 6 ([[2], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p149, Certificates.k13t6p149_check⟩

private theorem k13t6_cover309 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 13 6 ([[2], [2]] ++ P) := by
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
            exact k13t6_cover310
        · exact by
            intro _
            exact k13t6_cover311

private theorem k13t6_cover312 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 13 6 ([[2], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p150, Certificates.k13t6p150_check⟩

private theorem k13t6_cover313 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 13 6 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover314 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 13 6 ([[2], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover315 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 13 6 ([[2], [3]] ++ P) := by
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

private theorem k13t6_cover316 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 13 6 ([[2], [4]] ++ P) := by
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

private theorem k13t6_cover317 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 13 6 ([[2], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq308 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [2] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([[2]] ++ (([] ++ tail) :: P))) :=
by
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 3] ∧ LexLE [1, 1, 3] [3, 1, 1])) h)
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
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 2] ∧ LexLE [1, 2, 2] [2, 2, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [1, 3, 1] ∧ LexLE [1, 3, 1] [1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [1, 4] ∧ LexLE [1, 4] [4, 1])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover309
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
                    intro _
                    exact k13t6_cover312
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover313
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover314
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover315
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [2] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 2] ∧ LexLE [3, 2] [2, 3])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover316
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover317
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover307 : ∀ P ∈ pathPatterns 4 5 [2], HasCheckedCertificate 13 6 ([[2]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq308


private theorem k13t6_cover318 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 1, 2], HasCheckedCertificate 13 6 ([[2, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t6p151, Certificates.k13t6p151_check⟩

private theorem k13t6_cover319 : ∀ P ∈ pathPatterns 1 1 [2, 1, 1, 2], HasCheckedCertificate 13 6 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover320 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 3], HasCheckedCertificate 13 6 ([[2, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover321 : ∀ P ∈ pathPatterns 2 2 [2, 1, 2], HasCheckedCertificate 13 6 ([[2, 1, 2]] ++ P) := by
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
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [2] ∧ LexLE [2] [2])) h)

private theorem k13t6_cover322 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2, 2], HasCheckedCertificate 13 6 ([[2, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover323 : ∀ P ∈ pathPatterns 2 1 [2, 1, 3], HasCheckedCertificate 13 6 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover324 : ∀ P ∈ pathPatterns 2 0 [2, 1, 4], HasCheckedCertificate 13 6 ([[2, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover326 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 6 ([[2, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t6_cover325 : ∀ P ∈ pathPatterns 3 3 [2, 2], HasCheckedCertificate 13 6 ([[2, 2]] ++ P) := by
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
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover326
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover327 : ∀ P ∈ pathPatterns 2 1 [2, 2, 2], HasCheckedCertificate 13 6 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k13t6_cover328 : ∀ P ∈ pathPatterns 2 0 [2, 2, 3], HasCheckedCertificate 13 6 ([[2, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover329 : ∀ P ∈ pathPatterns 3 2 [2, 3], HasCheckedCertificate 13 6 ([[2, 3]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 3] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover330 : ∀ P ∈ pathPatterns 2 0 [2, 3, 2], HasCheckedCertificate 13 6 ([[2, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover331 : ∀ P ∈ pathPatterns 3 1 [2, 4], HasCheckedCertificate 13 6 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 4] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover332 : ∀ P ∈ pathPatterns 3 0 [2, 5], HasCheckedCertificate 13 6 ([[2, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq306 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([2] ++ tail) ∧ LexLE ([2] ++ tail) ([2] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([2] ++ tail).length) (7 - ([2] ++ tail).sum) ([2] ++ tail),
      HasCheckedCertificate 13 6 ([] ++ (([2] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover307
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
                          intro _
                          exact k13t6_cover318
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover319
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 2, 1] ∧ LexLE [2, 1, 1, 2, 1] [1, 2, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover320
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover321
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1, 1] ∧ LexLE [2, 1, 2, 1, 1] [1, 1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover322
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover323
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 3, 1] ∧ LexLE [2, 1, 3, 1] [1, 3, 1, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover324
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover325
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 1, 1] ∧ LexLE [2, 2, 1, 1, 1] [1, 1, 1, 2, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1, 2] ∧ LexLE [2, 2, 1, 2] [2, 1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover327
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 2, 1] ∧ LexLE [2, 2, 2, 1] [1, 2, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover328
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover329
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1, 1] ∧ LexLE [2, 3, 1, 1] [1, 1, 3, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover330
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover331
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 4, 1] ∧ LexLE [2, 4, 1] [1, 4, 2])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover332
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover334 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 13 6 ([[3], [3]] ++ P) := by
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

private theorem k13t6_cover335 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 13 6 ([[3], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover333 : ∀ P ∈ pathPatterns 4 4 [3], HasCheckedCertificate 13 6 ([[3]] ++ P) := by
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
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [1, 3] ∧ LexLE [1, 3] [3, 1])) h)
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
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [3] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [2, 2] ∧ LexLE [2, 2] [2, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover334
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [3] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t6_cover335
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover336 : ∀ P ∈ pathPatterns 2 0 [3, 1, 3], HasCheckedCertificate 13 6 ([[3, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover337 : ∀ P ∈ pathPatterns 3 1 [3, 3], HasCheckedCertificate 13 6 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [3, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover338 : ∀ P ∈ pathPatterns 3 0 [3, 4], HasCheckedCertificate 13 6 ([[3, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_cover339 : ∀ P ∈ pathPatterns 4 3 [4], HasCheckedCertificate 13 6 ([[4]] ++ P) := by
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
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [4] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [2] ∧ LexLE [2] [2])) h)
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [4] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [4] [3] ∧ LexLE [3] [3])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover340 : ∀ P ∈ pathPatterns 4 2 [5], HasCheckedCertificate 13 6 ([[5]] ++ P) := by
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
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [5] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [5] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover341 : ∀ P ∈ pathPatterns 4 1 [6], HasCheckedCertificate 13 6 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [6] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t6_cover342 : ∀ P ∈ pathPatterns 4 0 [7], HasCheckedCertificate 13 6 ([[7]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [7] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t6_seq2 : amountSequenceForall 5 7 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (7 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 6 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t6_cover3
  · intro q
    fin_cases q
    · exact k13t6_seq187

    · exact k13t6_seq306

    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover333
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
                            fin_cases q
                            · exact by
                                intro h
                                exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 1, 1] ∧ LexLE [3, 1, 1, 1, 1] [1, 1, 1, 1, 3])) h)
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 1, 2] ∧ LexLE [3, 1, 1, 2] [2, 1, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2] ∧ LexLE [3, 1, 2] [2, 1, 3])) h)
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 1, 2, 1] ∧ LexLE [3, 1, 2, 1] [1, 2, 1, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t6_cover336
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
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 1, 1] ∧ LexLE [3, 2, 1, 1] [1, 1, 2, 3])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 2, 2] ∧ LexLE [3, 2, 2] [2, 2, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover337
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [3, 3, 1] ∧ LexLE [3, 3, 1] [1, 3, 3])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t6_cover338
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover339
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
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 1, 1] ∧ LexLE [4, 1, 1, 1] [1, 1, 1, 4])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 1, 2] ∧ LexLE [4, 1, 2] [2, 1, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 2] ∧ LexLE [4, 2] [2, 4])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [4, 2, 1] ∧ LexLE [4, 2, 1] [1, 2, 4])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 3] ∧ LexLE [4, 3] [3, 4])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover340
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [] [5, 1, 1] ∧ LexLE [5, 1, 1] [1, 1, 5])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 2] ∧ LexLE [5, 2] [2, 5])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover341
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [6, 1] ∧ LexLE [6, 1] [1, 6])) h)
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t6_cover342
        · intro q
          exact Fin.elim0 q

private theorem k13t6_cover1 : ∀ P ∈ pathPatterns 6 7 [], HasCheckedCertificate 13 6 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t6_seq2


theorem coverage_k13_t6 :
    ∀ P ∈ pathPatterns 6 7, HasCheckedCertificate 13 6 P :=
  k13t6_cover1

private theorem k13t7_cover12 : ∀ P ∈ pathPatterns 0 6 [], HasCheckedCertificate 13 7 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p0, Certificates.k13t7p0_check⟩

private theorem k13t7_cover11 : ∀ P ∈ pathPatterns 1 6 [], HasCheckedCertificate 13 7 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k13t7_cover12

private theorem k13t7_cover13 : ∀ P ∈ pathPatterns 0 5 [1], HasCheckedCertificate 13 7 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p1, Certificates.k13t7p1_check⟩

private theorem k13t7_cover14 : ∀ P ∈ pathPatterns 0 4 [2], HasCheckedCertificate 13 7 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p2, Certificates.k13t7p2_check⟩

private theorem k13t7_cover15 : ∀ P ∈ pathPatterns 0 3 [3], HasCheckedCertificate 13 7 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p3, Certificates.k13t7p3_check⟩

private theorem k13t7_cover16 : ∀ P ∈ pathPatterns 0 2 [4], HasCheckedCertificate 13 7 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p4, Certificates.k13t7p4_check⟩

private theorem k13t7_cover17 : ∀ P ∈ pathPatterns 0 1 [5], HasCheckedCertificate 13 7 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p5, Certificates.k13t7p5_check⟩

private theorem k13t7_cover18 : ∀ P ∈ pathPatterns 0 0 [6], HasCheckedCertificate 13 7 ([[], [], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p6, Certificates.k13t7p6_check⟩

private theorem k13t7_cover10 : ∀ P ∈ pathPatterns 2 6 [], HasCheckedCertificate 13 7 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k13t7_cover11
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k13t7_cover13
        · exact by
            intro _
            exact k13t7_cover14
        · exact by
            intro _
            exact k13t7_cover15
        · exact by
            intro _
            exact k13t7_cover16
        · exact by
            intro _
            exact k13t7_cover17
        · exact by
            intro _
            exact k13t7_cover18

private theorem k13t7_cover19 : ∀ P ∈ pathPatterns 1 5 [1], HasCheckedCertificate 13 7 ([[], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover20 : ∀ P ∈ pathPatterns 0 4 [1, 1], HasCheckedCertificate 13 7 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p7, Certificates.k13t7p7_check⟩

private theorem k13t7_cover21 : ∀ P ∈ pathPatterns 0 3 [1, 2], HasCheckedCertificate 13 7 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p8, Certificates.k13t7p8_check⟩

private theorem k13t7_cover22 : ∀ P ∈ pathPatterns 0 2 [1, 3], HasCheckedCertificate 13 7 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p9, Certificates.k13t7p9_check⟩

private theorem k13t7_cover23 : ∀ P ∈ pathPatterns 0 1 [1, 4], HasCheckedCertificate 13 7 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p10, Certificates.k13t7p10_check⟩

private theorem k13t7_cover24 : ∀ P ∈ pathPatterns 0 0 [1, 5], HasCheckedCertificate 13 7 ([[], [], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p11, Certificates.k13t7p11_check⟩

private theorem k13t7_cover25 : ∀ P ∈ pathPatterns 1 4 [2], HasCheckedCertificate 13 7 ([[], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover26 : ∀ P ∈ pathPatterns 0 2 [2, 2], HasCheckedCertificate 13 7 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p12, Certificates.k13t7p12_check⟩

private theorem k13t7_cover27 : ∀ P ∈ pathPatterns 0 1 [2, 3], HasCheckedCertificate 13 7 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p13, Certificates.k13t7p13_check⟩

private theorem k13t7_cover28 : ∀ P ∈ pathPatterns 0 0 [2, 4], HasCheckedCertificate 13 7 ([[], [], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p14, Certificates.k13t7p14_check⟩

private theorem k13t7_cover29 : ∀ P ∈ pathPatterns 1 3 [3], HasCheckedCertificate 13 7 ([[], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover30 : ∀ P ∈ pathPatterns 0 0 [3, 3], HasCheckedCertificate 13 7 ([[], [], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p15, Certificates.k13t7p15_check⟩

private theorem k13t7_cover31 : ∀ P ∈ pathPatterns 1 2 [4], HasCheckedCertificate 13 7 ([[], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover32 : ∀ P ∈ pathPatterns 1 1 [5], HasCheckedCertificate 13 7 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover33 : ∀ P ∈ pathPatterns 1 0 [6], HasCheckedCertificate 13 7 ([[], [], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover9 : ∀ P ∈ pathPatterns 3 6 [], HasCheckedCertificate 13 7 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k13t7_cover10
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover19
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t7_cover20
              · exact by
                  intro _
                  exact k13t7_cover21
              · exact by
                  intro _
                  exact k13t7_cover22
              · exact by
                  intro _
                  exact k13t7_cover23
              · exact by
                  intro _
                  exact k13t7_cover24
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover25
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t7_cover26
              · exact by
                  intro _
                  exact k13t7_cover27
              · exact by
                  intro _
                  exact k13t7_cover28
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover29
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
                  exact k13t7_cover30
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover31
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
                exact k13t7_cover32
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [5, 1] ∧ LexLE [5, 1] [1, 5])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover33
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover35 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 13 7 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p16, Certificates.k13t7p16_check⟩

private theorem k13t7_cover36 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 13 7 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p17, Certificates.k13t7p17_check⟩

private theorem k13t7_cover37 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 13 7 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p18, Certificates.k13t7p18_check⟩

private theorem k13t7_cover38 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 13 7 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p19, Certificates.k13t7p19_check⟩

private theorem k13t7_cover39 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 13 7 ([[], [], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p20, Certificates.k13t7p20_check⟩

private theorem k13t7_cover34 : ∀ P ∈ pathPatterns 2 5 [1], HasCheckedCertificate 13 7 ([[], [], [], [1]] ++ P) := by
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
            exact k13t7_cover35
        · exact by
            intro _
            exact k13t7_cover36
        · exact by
            intro _
            exact k13t7_cover37
        · exact by
            intro _
            exact k13t7_cover38
        · exact by
            intro _
            exact k13t7_cover39

private theorem k13t7_cover40 : ∀ P ∈ pathPatterns 1 4 [1, 1], HasCheckedCertificate 13 7 ([[], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover41 : ∀ P ∈ pathPatterns 0 3 [1, 1, 1], HasCheckedCertificate 13 7 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p21, Certificates.k13t7p21_check⟩

private theorem k13t7_cover42 : ∀ P ∈ pathPatterns 0 2 [1, 1, 2], HasCheckedCertificate 13 7 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p22, Certificates.k13t7p22_check⟩

private theorem k13t7_cover43 : ∀ P ∈ pathPatterns 0 1 [1, 1, 3], HasCheckedCertificate 13 7 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p23, Certificates.k13t7p23_check⟩

private theorem k13t7_cover44 : ∀ P ∈ pathPatterns 0 0 [1, 1, 4], HasCheckedCertificate 13 7 ([[], [], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p24, Certificates.k13t7p24_check⟩

private theorem k13t7_cover45 : ∀ P ∈ pathPatterns 1 3 [1, 2], HasCheckedCertificate 13 7 ([[], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover46 : ∀ P ∈ pathPatterns 0 2 [1, 2, 1], HasCheckedCertificate 13 7 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p25, Certificates.k13t7p25_check⟩

private theorem k13t7_cover47 : ∀ P ∈ pathPatterns 0 1 [1, 2, 2], HasCheckedCertificate 13 7 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p26, Certificates.k13t7p26_check⟩

private theorem k13t7_cover48 : ∀ P ∈ pathPatterns 0 0 [1, 2, 3], HasCheckedCertificate 13 7 ([[], [], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p27, Certificates.k13t7p27_check⟩

private theorem k13t7_cover49 : ∀ P ∈ pathPatterns 1 2 [1, 3], HasCheckedCertificate 13 7 ([[], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover50 : ∀ P ∈ pathPatterns 0 1 [1, 3, 1], HasCheckedCertificate 13 7 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p28, Certificates.k13t7p28_check⟩

private theorem k13t7_cover51 : ∀ P ∈ pathPatterns 0 0 [1, 3, 2], HasCheckedCertificate 13 7 ([[], [], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p29, Certificates.k13t7p29_check⟩

private theorem k13t7_cover52 : ∀ P ∈ pathPatterns 1 1 [1, 4], HasCheckedCertificate 13 7 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover53 : ∀ P ∈ pathPatterns 0 0 [1, 4, 1], HasCheckedCertificate 13 7 ([[], [], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p30, Certificates.k13t7p30_check⟩

private theorem k13t7_cover54 : ∀ P ∈ pathPatterns 1 0 [1, 5], HasCheckedCertificate 13 7 ([[], [], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover56 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 7 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p31, Certificates.k13t7p31_check⟩

private theorem k13t7_cover57 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 7 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p32, Certificates.k13t7p32_check⟩

private theorem k13t7_cover58 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 7 ([[], [], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p33, Certificates.k13t7p33_check⟩

private theorem k13t7_cover55 : ∀ P ∈ pathPatterns 2 4 [2], HasCheckedCertificate 13 7 ([[], [], [], [2]] ++ P) := by
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
            exact k13t7_cover56
        · exact by
            intro _
            exact k13t7_cover57
        · exact by
            intro _
            exact k13t7_cover58

private theorem k13t7_cover59 : ∀ P ∈ pathPatterns 0 1 [2, 1, 2], HasCheckedCertificate 13 7 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p34, Certificates.k13t7p34_check⟩

private theorem k13t7_cover60 : ∀ P ∈ pathPatterns 0 0 [2, 1, 3], HasCheckedCertificate 13 7 ([[], [], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p35, Certificates.k13t7p35_check⟩

private theorem k13t7_cover61 : ∀ P ∈ pathPatterns 1 2 [2, 2], HasCheckedCertificate 13 7 ([[], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover62 : ∀ P ∈ pathPatterns 0 0 [2, 2, 2], HasCheckedCertificate 13 7 ([[], [], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p36, Certificates.k13t7p36_check⟩

private theorem k13t7_cover63 : ∀ P ∈ pathPatterns 1 1 [2, 3], HasCheckedCertificate 13 7 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover64 : ∀ P ∈ pathPatterns 1 0 [2, 4], HasCheckedCertificate 13 7 ([[], [], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover66 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 7 ([[], [], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p37, Certificates.k13t7p37_check⟩

private theorem k13t7_cover65 : ∀ P ∈ pathPatterns 2 3 [3], HasCheckedCertificate 13 7 ([[], [], [], [3]] ++ P) := by
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
            exact k13t7_cover66

private theorem k13t7_cover67 : ∀ P ∈ pathPatterns 1 0 [3, 3], HasCheckedCertificate 13 7 ([[], [], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover68 : ∀ P ∈ pathPatterns 2 2 [4], HasCheckedCertificate 13 7 ([[], [], [], [4]] ++ P) := by
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

private theorem k13t7_cover69 : ∀ P ∈ pathPatterns 2 1 [5], HasCheckedCertificate 13 7 ([[], [], [], [5]] ++ P) := by
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

private theorem k13t7_cover70 : ∀ P ∈ pathPatterns 2 0 [6], HasCheckedCertificate 13 7 ([[], [], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq8 : amountSequenceForall 3 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover9
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover34
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover40
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover41
                · exact by
                    intro _
                    exact k13t7_cover42
                · exact by
                    intro _
                    exact k13t7_cover43
                · exact by
                    intro _
                    exact k13t7_cover44
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover45
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover46
                · exact by
                    intro _
                    exact k13t7_cover47
                · exact by
                    intro _
                    exact k13t7_cover48
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover49
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover50
                · exact by
                    intro _
                    exact k13t7_cover51
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover52
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover53
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover54
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover55
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
                    exact k13t7_cover59
                · exact by
                    intro _
                    exact k13t7_cover60
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover61
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                · exact by
                    intro _
                    exact k13t7_cover62
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover63
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 3, 1] ∧ LexLE [2, 3, 1] [1, 3, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover64
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover65
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
                  exact k13t7_cover67
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover68
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
            exact k13t7_cover69
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
            exact k13t7_cover70
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover7 : ∀ P ∈ pathPatterns 4 6 [], HasCheckedCertificate 13 7 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq8


private theorem k13t7_cover73 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 13 7 ([[], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover74 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 13 7 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p38, Certificates.k13t7p38_check⟩

private theorem k13t7_cover75 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 13 7 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p39, Certificates.k13t7p39_check⟩

private theorem k13t7_cover76 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 13 7 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p40, Certificates.k13t7p40_check⟩

private theorem k13t7_cover77 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 13 7 ([[], [], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p41, Certificates.k13t7p41_check⟩

private theorem k13t7_cover78 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 13 7 ([[], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover79 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 13 7 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p42, Certificates.k13t7p42_check⟩

private theorem k13t7_cover80 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 13 7 ([[], [], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p43, Certificates.k13t7p43_check⟩

private theorem k13t7_cover81 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 13 7 ([[], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover82 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 13 7 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover83 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 13 7 ([[], [], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover72 : ∀ P ∈ pathPatterns 3 5 [1], HasCheckedCertificate 13 7 ([[], [], [1]] ++ P) := by
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
                exact k13t7_cover73
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t7_cover74
              · exact by
                  intro _
                  exact k13t7_cover75
              · exact by
                  intro _
                  exact k13t7_cover76
              · exact by
                  intro _
                  exact k13t7_cover77
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover78
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t7_cover79
              · exact by
                  intro _
                  exact k13t7_cover80
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover81
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
                exact k13t7_cover82
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover83
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover85 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 7 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p44, Certificates.k13t7p44_check⟩

private theorem k13t7_cover86 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 7 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p45, Certificates.k13t7p45_check⟩

private theorem k13t7_cover87 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 7 ([[], [], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p46, Certificates.k13t7p46_check⟩

private theorem k13t7_cover84 : ∀ P ∈ pathPatterns 2 4 [1, 1], HasCheckedCertificate 13 7 ([[], [], [1, 1]] ++ P) := by
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
            exact k13t7_cover85
        · exact by
            intro _
            exact k13t7_cover86
        · exact by
            intro _
            exact k13t7_cover87

private theorem k13t7_cover88 : ∀ P ∈ pathPatterns 1 3 [1, 1, 1], HasCheckedCertificate 13 7 ([[], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover89 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1, 1], HasCheckedCertificate 13 7 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p47, Certificates.k13t7p47_check⟩

private theorem k13t7_cover90 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 2], HasCheckedCertificate 13 7 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p48, Certificates.k13t7p48_check⟩

private theorem k13t7_cover91 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 3], HasCheckedCertificate 13 7 ([[], [], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p49, Certificates.k13t7p49_check⟩

private theorem k13t7_cover92 : ∀ P ∈ pathPatterns 1 2 [1, 1, 2], HasCheckedCertificate 13 7 ([[], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover93 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2, 1], HasCheckedCertificate 13 7 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p50, Certificates.k13t7p50_check⟩

private theorem k13t7_cover94 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 2], HasCheckedCertificate 13 7 ([[], [], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p51, Certificates.k13t7p51_check⟩

private theorem k13t7_cover95 : ∀ P ∈ pathPatterns 1 1 [1, 1, 3], HasCheckedCertificate 13 7 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover96 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3, 1], HasCheckedCertificate 13 7 ([[], [], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p52, Certificates.k13t7p52_check⟩

private theorem k13t7_cover97 : ∀ P ∈ pathPatterns 1 0 [1, 1, 4], HasCheckedCertificate 13 7 ([[], [], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover99 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 7 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p53, Certificates.k13t7p53_check⟩

private theorem k13t7_cover100 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 7 ([[], [], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p54, Certificates.k13t7p54_check⟩

private theorem k13t7_cover98 : ∀ P ∈ pathPatterns 2 3 [1, 2], HasCheckedCertificate 13 7 ([[], [], [1, 2]] ++ P) := by
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
            exact k13t7_cover99
        · exact by
            intro _
            exact k13t7_cover100

private theorem k13t7_cover101 : ∀ P ∈ pathPatterns 1 2 [1, 2, 1], HasCheckedCertificate 13 7 ([[], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover102 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1, 2], HasCheckedCertificate 13 7 ([[], [], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p55, Certificates.k13t7p55_check⟩

private theorem k13t7_cover103 : ∀ P ∈ pathPatterns 1 1 [1, 2, 2], HasCheckedCertificate 13 7 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover104 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2, 1], HasCheckedCertificate 13 7 ([[], [], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p56, Certificates.k13t7p56_check⟩

private theorem k13t7_cover105 : ∀ P ∈ pathPatterns 1 0 [1, 2, 3], HasCheckedCertificate 13 7 ([[], [], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover107 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[], [], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p57, Certificates.k13t7p57_check⟩

private theorem k13t7_cover106 : ∀ P ∈ pathPatterns 2 2 [1, 3], HasCheckedCertificate 13 7 ([[], [], [1, 3]] ++ P) := by
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
            exact k13t7_cover107

private theorem k13t7_cover108 : ∀ P ∈ pathPatterns 1 1 [1, 3, 1], HasCheckedCertificate 13 7 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover109 : ∀ P ∈ pathPatterns 1 0 [1, 3, 2], HasCheckedCertificate 13 7 ([[], [], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover110 : ∀ P ∈ pathPatterns 2 1 [1, 4], HasCheckedCertificate 13 7 ([[], [], [1, 4]] ++ P) := by
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

private theorem k13t7_cover111 : ∀ P ∈ pathPatterns 1 0 [1, 4, 1], HasCheckedCertificate 13 7 ([[], [], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover112 : ∀ P ∈ pathPatterns 2 0 [1, 5], HasCheckedCertificate 13 7 ([[], [], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq71 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 13 7 ([[], []] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover72
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover84
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover88
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover89
                · exact by
                    intro _
                    exact k13t7_cover90
                · exact by
                    intro _
                    exact k13t7_cover91
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover92
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover93
                · exact by
                    intro _
                    exact k13t7_cover94
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover95
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover96
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover97
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover98
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover101
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    intro _
                    exact k13t7_cover102
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover103
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover104
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover105
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover106
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover108
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [1, 3, 1, 1] ∧ LexLE [1, 3, 1, 1] [1, 1, 3, 1])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover109
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover110
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover111
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover112
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover114 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 13 7 ([[], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover115 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 13 7 ([[], [], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p58, Certificates.k13t7p58_check⟩

private theorem k13t7_cover116 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 7 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover117 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 7 ([[], [], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover113 : ∀ P ∈ pathPatterns 3 4 [2], HasCheckedCertificate 13 7 ([[], [], [2]] ++ P) := by
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
                exact k13t7_cover114
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t7_cover115
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover116
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover117
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover118 : ∀ P ∈ pathPatterns 0 0 [2, 1, 1, 2], HasCheckedCertificate 13 7 ([[], [], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p59, Certificates.k13t7p59_check⟩

private theorem k13t7_cover119 : ∀ P ∈ pathPatterns 1 1 [2, 1, 2], HasCheckedCertificate 13 7 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover120 : ∀ P ∈ pathPatterns 1 0 [2, 1, 3], HasCheckedCertificate 13 7 ([[], [], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover121 : ∀ P ∈ pathPatterns 2 2 [2, 2], HasCheckedCertificate 13 7 ([[], [], [2, 2]] ++ P) := by
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

private theorem k13t7_cover122 : ∀ P ∈ pathPatterns 1 0 [2, 2, 2], HasCheckedCertificate 13 7 ([[], [], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover123 : ∀ P ∈ pathPatterns 2 1 [2, 3], HasCheckedCertificate 13 7 ([[], [], [2, 3]] ++ P) := by
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

private theorem k13t7_cover124 : ∀ P ∈ pathPatterns 2 0 [2, 4], HasCheckedCertificate 13 7 ([[], [], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover126 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 7 ([[], [], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover125 : ∀ P ∈ pathPatterns 3 3 [3], HasCheckedCertificate 13 7 ([[], [], [3]] ++ P) := by
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
                exact k13t7_cover126
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover127 : ∀ P ∈ pathPatterns 2 0 [3, 3], HasCheckedCertificate 13 7 ([[], [], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover128 : ∀ P ∈ pathPatterns 3 2 [4], HasCheckedCertificate 13 7 ([[], [], [4]] ++ P) := by
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

private theorem k13t7_cover129 : ∀ P ∈ pathPatterns 3 1 [5], HasCheckedCertificate 13 7 ([[], [], [5]] ++ P) := by
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

private theorem k13t7_cover130 : ∀ P ∈ pathPatterns 3 0 [6], HasCheckedCertificate 13 7 ([[], [], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq6 : amountSequenceForall 4 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover7
  · intro q
    fin_cases q
    · exact k13t7_seq71

    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover113
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
                          exact k13t7_cover118
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover119
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 2, 1] ∧ LexLE [2, 1, 2, 1] [1, 2, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover120
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover121
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
                        exact k13t7_cover122
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover123
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
                  exact k13t7_cover124
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover125
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
                  exact k13t7_cover127
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover128
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
            exact k13t7_cover129
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
            exact k13t7_cover130
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover5 : ∀ P ∈ pathPatterns 5 6 [], HasCheckedCertificate 13 7 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq6


private theorem k13t7_cover135 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 13 7 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p60, Certificates.k13t7p60_check⟩

private theorem k13t7_cover136 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 7 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p61, Certificates.k13t7p61_check⟩

private theorem k13t7_cover137 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 7 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p62, Certificates.k13t7p62_check⟩

private theorem k13t7_cover138 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 7 ([[], [1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p63, Certificates.k13t7p63_check⟩

private theorem k13t7_cover134 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 13 7 ([[], [1], [1]] ++ P) := by
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
            exact k13t7_cover135
        · exact by
            intro _
            exact k13t7_cover136
        · exact by
            intro _
            exact k13t7_cover137
        · exact by
            intro _
            exact k13t7_cover138

private theorem k13t7_cover139 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 13 7 ([[], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover140 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 13 7 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p64, Certificates.k13t7p64_check⟩

private theorem k13t7_cover141 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 13 7 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p65, Certificates.k13t7p65_check⟩

private theorem k13t7_cover142 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 13 7 ([[], [1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p66, Certificates.k13t7p66_check⟩

private theorem k13t7_cover143 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 13 7 ([[], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover144 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 13 7 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p67, Certificates.k13t7p67_check⟩

private theorem k13t7_cover145 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 13 7 ([[], [1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p68, Certificates.k13t7p68_check⟩

private theorem k13t7_cover146 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 13 7 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover147 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 13 7 ([[], [1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p69, Certificates.k13t7p69_check⟩

private theorem k13t7_cover148 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 13 7 ([[], [1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover150 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 7 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p70, Certificates.k13t7p70_check⟩

private theorem k13t7_cover151 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 7 ([[], [1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p71, Certificates.k13t7p71_check⟩

private theorem k13t7_cover149 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 13 7 ([[], [1], [2]] ++ P) := by
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
            exact k13t7_cover150
        · exact by
            intro _
            exact k13t7_cover151

private theorem k13t7_cover152 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 13 7 ([[], [1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p72, Certificates.k13t7p72_check⟩

private theorem k13t7_cover153 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 13 7 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover154 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 13 7 ([[], [1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover155 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 13 7 ([[], [1], [3]] ++ P) := by
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

private theorem k13t7_cover156 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 13 7 ([[], [1], [4]] ++ P) := by
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

private theorem k13t7_cover157 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 13 7 ([[], [1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq133 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([[], [1]] ++ (([] ++ tail) :: P))) :=
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
            exact k13t7_cover134
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover139
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover140
                · exact by
                    intro _
                    exact k13t7_cover141
                · exact by
                    intro _
                    exact k13t7_cover142
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover143
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover144
                · exact by
                    intro _
                    exact k13t7_cover145
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover146
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t7_cover147
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover148
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover149
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
                    exact k13t7_cover152
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover153
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover154
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover155
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
            exact k13t7_cover156
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
            exact k13t7_cover157
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover132 : ∀ P ∈ pathPatterns 4 5 [1], HasCheckedCertificate 13 7 ([[], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq133


private theorem k13t7_cover159 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 13 7 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p73, Certificates.k13t7p73_check⟩

private theorem k13t7_cover160 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 13 7 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p74, Certificates.k13t7p74_check⟩

private theorem k13t7_cover161 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 13 7 ([[], [1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p75, Certificates.k13t7p75_check⟩

private theorem k13t7_cover162 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 13 7 ([[], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover163 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 13 7 ([[], [1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p76, Certificates.k13t7p76_check⟩

private theorem k13t7_cover164 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 7 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover165 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 7 ([[], [1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover158 : ∀ P ∈ pathPatterns 3 4 [1, 1], HasCheckedCertificate 13 7 ([[], [1, 1]] ++ P) := by
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
                  exact k13t7_cover159
              · exact by
                  intro _
                  exact k13t7_cover160
              · exact by
                  intro _
                  exact k13t7_cover161
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover162
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t7_cover163
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover164
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover165
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover167 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 7 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p77, Certificates.k13t7p77_check⟩

private theorem k13t7_cover168 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 7 ([[], [1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p78, Certificates.k13t7p78_check⟩

private theorem k13t7_cover166 : ∀ P ∈ pathPatterns 2 3 [1, 1, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 1]] ++ P) := by
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
            exact k13t7_cover167
        · exact by
            intro _
            exact k13t7_cover168

private theorem k13t7_cover169 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover170 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p79, Certificates.k13t7p79_check⟩

private theorem k13t7_cover171 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 2], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p80, Certificates.k13t7p80_check⟩

private theorem k13t7_cover172 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 2], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover173 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p81, Certificates.k13t7p81_check⟩

private theorem k13t7_cover174 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 3], HasCheckedCertificate 13 7 ([[], [1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover176 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[], [1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p82, Certificates.k13t7p82_check⟩

private theorem k13t7_cover175 : ∀ P ∈ pathPatterns 2 2 [1, 1, 2], HasCheckedCertificate 13 7 ([[], [1, 1, 2]] ++ P) := by
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
            exact k13t7_cover176

private theorem k13t7_cover177 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover178 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p83, Certificates.k13t7p83_check⟩

private theorem k13t7_cover179 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 2], HasCheckedCertificate 13 7 ([[], [1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover180 : ∀ P ∈ pathPatterns 2 1 [1, 1, 3], HasCheckedCertificate 13 7 ([[], [1, 1, 3]] ++ P) := by
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

private theorem k13t7_cover181 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3, 1], HasCheckedCertificate 13 7 ([[], [1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover182 : ∀ P ∈ pathPatterns 2 0 [1, 1, 4], HasCheckedCertificate 13 7 ([[], [1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover184 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 13 7 ([[], [1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p84, Certificates.k13t7p84_check⟩

private theorem k13t7_cover185 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 7 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover186 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 7 ([[], [1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover183 : ∀ P ∈ pathPatterns 3 3 [1, 2], HasCheckedCertificate 13 7 ([[], [1, 2]] ++ P) := by
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
                  exact k13t7_cover184
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover185
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover186
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover188 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[], [1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p85, Certificates.k13t7p85_check⟩

private theorem k13t7_cover187 : ∀ P ∈ pathPatterns 2 2 [1, 2, 1], HasCheckedCertificate 13 7 ([[], [1, 2, 1]] ++ P) := by
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
            exact k13t7_cover188

private theorem k13t7_cover189 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1, 2], HasCheckedCertificate 13 7 ([[], [1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover190 : ∀ P ∈ pathPatterns 2 1 [1, 2, 2], HasCheckedCertificate 13 7 ([[], [1, 2, 2]] ++ P) := by
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

private theorem k13t7_cover191 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2, 1], HasCheckedCertificate 13 7 ([[], [1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover192 : ∀ P ∈ pathPatterns 2 0 [1, 2, 3], HasCheckedCertificate 13 7 ([[], [1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover194 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 7 ([[], [1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover193 : ∀ P ∈ pathPatterns 3 2 [1, 3], HasCheckedCertificate 13 7 ([[], [1, 3]] ++ P) := by
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
                exact k13t7_cover194
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover195 : ∀ P ∈ pathPatterns 2 1 [1, 3, 1], HasCheckedCertificate 13 7 ([[], [1, 3, 1]] ++ P) := by
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

private theorem k13t7_cover196 : ∀ P ∈ pathPatterns 2 0 [1, 3, 2], HasCheckedCertificate 13 7 ([[], [1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover197 : ∀ P ∈ pathPatterns 3 1 [1, 4], HasCheckedCertificate 13 7 ([[], [1, 4]] ++ P) := by
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

private theorem k13t7_cover198 : ∀ P ∈ pathPatterns 2 0 [1, 4, 1], HasCheckedCertificate 13 7 ([[], [1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover199 : ∀ P ∈ pathPatterns 3 0 [1, 5], HasCheckedCertificate 13 7 ([[], [1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq131 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 13 7 ([[]] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover132
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover158
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover166
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover169
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t7_cover170
                      · exact by
                          intro _
                          exact k13t7_cover171
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover172
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t7_cover173
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover174
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover175
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover177
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t7_cover178
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover179
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover180
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover181
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover182
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover183
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover187
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
                        exact k13t7_cover189
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover190
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover191
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover192
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover193
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover195
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
                  exact k13t7_cover196
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover197
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover198
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover199
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover202 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[], [2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p86, Certificates.k13t7p86_check⟩

private theorem k13t7_cover201 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 13 7 ([[], [2], [2]] ++ P) := by
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
            exact k13t7_cover202

private theorem k13t7_cover203 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 13 7 ([[], [2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover204 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 13 7 ([[], [2], [3]] ++ P) := by
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

private theorem k13t7_cover205 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 13 7 ([[], [2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover200 : ∀ P ∈ pathPatterns 4 4 [2], HasCheckedCertificate 13 7 ([[], [2]] ++ P) := by
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
                exact k13t7_cover201
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
                      exact k13t7_cover203
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover204
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
                exact k13t7_cover205
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover206 : ∀ P ∈ pathPatterns 1 0 [2, 1, 1, 2], HasCheckedCertificate 13 7 ([[], [2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover207 : ∀ P ∈ pathPatterns 2 1 [2, 1, 2], HasCheckedCertificate 13 7 ([[], [2, 1, 2]] ++ P) := by
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

private theorem k13t7_cover208 : ∀ P ∈ pathPatterns 2 0 [2, 1, 3], HasCheckedCertificate 13 7 ([[], [2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover209 : ∀ P ∈ pathPatterns 3 2 [2, 2], HasCheckedCertificate 13 7 ([[], [2, 2]] ++ P) := by
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

private theorem k13t7_cover210 : ∀ P ∈ pathPatterns 2 0 [2, 2, 2], HasCheckedCertificate 13 7 ([[], [2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover211 : ∀ P ∈ pathPatterns 3 1 [2, 3], HasCheckedCertificate 13 7 ([[], [2, 3]] ++ P) := by
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

private theorem k13t7_cover212 : ∀ P ∈ pathPatterns 3 0 [2, 4], HasCheckedCertificate 13 7 ([[], [2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover214 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 13 7 ([[], [3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover213 : ∀ P ∈ pathPatterns 4 3 [3], HasCheckedCertificate 13 7 ([[], [3]] ++ P) := by
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
                exact k13t7_cover214
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover215 : ∀ P ∈ pathPatterns 3 0 [3, 3], HasCheckedCertificate 13 7 ([[], [3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover216 : ∀ P ∈ pathPatterns 4 2 [4], HasCheckedCertificate 13 7 ([[], [4]] ++ P) := by
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

private theorem k13t7_cover217 : ∀ P ∈ pathPatterns 4 1 [5], HasCheckedCertificate 13 7 ([[], [5]] ++ P) := by
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

private theorem k13t7_cover218 : ∀ P ∈ pathPatterns 4 0 [6], HasCheckedCertificate 13 7 ([[], [6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq4 : amountSequenceForall 5 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover5
  · intro q
    fin_cases q
    · exact k13t7_seq131

    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover200
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
                              exact k13t7_cover206
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover207
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
                        exact k13t7_cover208
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover209
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
                        exact k13t7_cover210
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover211
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
                  exact k13t7_cover212
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover213
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
                  exact k13t7_cover215
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover216
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
            exact k13t7_cover217
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
            exact k13t7_cover218
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover3 : ∀ P ∈ pathPatterns 6 6 [], HasCheckedCertificate 13 7 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq4


private theorem k13t7_cover223 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 13 7 ([[1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover224 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 13 7 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p87, Certificates.k13t7p87_check⟩

private theorem k13t7_cover225 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 13 7 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p88, Certificates.k13t7p88_check⟩

private theorem k13t7_cover226 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 13 7 ([[1], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p89, Certificates.k13t7p89_check⟩

private theorem k13t7_cover227 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 13 7 ([[1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover228 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 13 7 ([[1], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p90, Certificates.k13t7p90_check⟩

private theorem k13t7_cover229 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 7 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover230 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 7 ([[1], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover222 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 13 7 ([[1], [1]] ++ P) := by
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
                exact k13t7_cover223
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t7_cover224
              · exact by
                  intro _
                  exact k13t7_cover225
              · exact by
                  intro _
                  exact k13t7_cover226
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover227
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t7_cover228
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover229
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover230
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover232 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 7 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p91, Certificates.k13t7p91_check⟩

private theorem k13t7_cover233 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 7 ([[1], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p92, Certificates.k13t7p92_check⟩

private theorem k13t7_cover231 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 13 7 ([[1], [1, 1]] ++ P) := by
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
            exact k13t7_cover232
        · exact by
            intro _
            exact k13t7_cover233

private theorem k13t7_cover234 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 13 7 ([[1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover235 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 13 7 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p93, Certificates.k13t7p93_check⟩

private theorem k13t7_cover236 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 13 7 ([[1], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p94, Certificates.k13t7p94_check⟩

private theorem k13t7_cover237 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 13 7 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover238 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 13 7 ([[1], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p95, Certificates.k13t7p95_check⟩

private theorem k13t7_cover239 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 13 7 ([[1], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover241 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[1], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p96, Certificates.k13t7p96_check⟩

private theorem k13t7_cover240 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 13 7 ([[1], [1, 2]] ++ P) := by
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
            exact k13t7_cover241

private theorem k13t7_cover242 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 13 7 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover243 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 13 7 ([[1], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover244 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 13 7 ([[1], [1, 3]] ++ P) := by
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

private theorem k13t7_cover245 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 13 7 ([[1], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover246 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 13 7 ([[1], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover248 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 7 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover249 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 7 ([[1], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover247 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 13 7 ([[1], [2]] ++ P) := by
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
                exact k13t7_cover248
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover249
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover250 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 13 7 ([[1], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover251 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 13 7 ([[1], [2, 2]] ++ P) := by
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

private theorem k13t7_cover252 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 13 7 ([[1], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover253 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 13 7 ([[1], [3]] ++ P) := by
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

private theorem k13t7_cover254 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 13 7 ([[1], [4]] ++ P) := by
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

private theorem k13t7_cover255 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 13 7 ([[1], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq221 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [1] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([[1]] ++ (([] ++ tail) :: P))) :=
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
            exact k13t7_cover222
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover231
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover234
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t7_cover235
                      · exact by
                          intro _
                          exact k13t7_cover236
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover237
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t7_cover238
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover239
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover240
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover242
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover243
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover244
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover245
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover246
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover247
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
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [1] [2, 1, 1, 1] ∧ LexLE [2, 1, 1, 1] [1, 1, 1, 2])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover250
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover251
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover252
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover253
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
                    constructor
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1] [3, 1, 1] ∧ LexLE [3, 1, 1] [1, 1, 3])) h)
                    · intro q
                      exact Fin.elim0 q
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
            exact k13t7_cover254
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
            exact k13t7_cover255
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover220 : ∀ P ∈ pathPatterns 5 5 [1], HasCheckedCertificate 13 7 ([[1]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq221


private theorem k13t7_cover257 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 13 7 ([[1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover258 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 13 7 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p97, Certificates.k13t7p97_check⟩

private theorem k13t7_cover259 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 13 7 ([[1, 1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p98, Certificates.k13t7p98_check⟩

private theorem k13t7_cover260 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 13 7 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover261 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 13 7 ([[1, 1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p99, Certificates.k13t7p99_check⟩

private theorem k13t7_cover262 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 13 7 ([[1, 1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover264 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[1, 1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p100, Certificates.k13t7p100_check⟩

private theorem k13t7_cover263 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 13 7 ([[1, 1], [2]] ++ P) := by
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
            exact k13t7_cover264

private theorem k13t7_cover265 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 13 7 ([[1, 1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover266 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 13 7 ([[1, 1], [3]] ++ P) := by
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

private theorem k13t7_cover267 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 13 7 ([[1, 1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover256 : ∀ P ∈ pathPatterns 4 4 [1, 1], HasCheckedCertificate 13 7 ([[1, 1]] ++ P) := by
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
                      exact k13t7_cover257
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t7_cover258
                    · exact by
                        intro _
                        exact k13t7_cover259
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t7_cover260
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t7_cover261
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t7_cover262
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover263
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t7_cover265
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover266
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover267
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover269 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 13 7 ([[1, 1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p101, Certificates.k13t7p101_check⟩

private theorem k13t7_cover270 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 7 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover271 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 7 ([[1, 1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover268 : ∀ P ∈ pathPatterns 3 3 [1, 1, 1], HasCheckedCertificate 13 7 ([[1, 1, 1]] ++ P) := by
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
                  intro _
                  exact k13t7_cover269
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover270
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover271
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover273 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 7 ([[1, 1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p102, Certificates.k13t7p102_check⟩

private theorem k13t7_cover272 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1, 1], HasCheckedCertificate 13 7 ([[1, 1, 1, 1]] ++ P) := by
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
        · exact by
            intro _
            exact k13t7_cover273

private theorem k13t7_cover274 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1, 1], HasCheckedCertificate 13 7 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover275 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1, 1], HasCheckedCertificate 13 7 ([[1, 1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t7p103, Certificates.k13t7p103_check⟩

private theorem k13t7_cover276 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 2], HasCheckedCertificate 13 7 ([[1, 1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover277 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 2], HasCheckedCertificate 13 7 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [1] ∧ LexLE [1] [1])) h)

private theorem k13t7_cover278 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2, 1], HasCheckedCertificate 13 7 ([[1, 1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover279 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 3], HasCheckedCertificate 13 7 ([[1, 1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover281 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 7 ([[1, 1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover280 : ∀ P ∈ pathPatterns 3 2 [1, 1, 2], HasCheckedCertificate 13 7 ([[1, 1, 2]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover281
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover282 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2, 1], HasCheckedCertificate 13 7 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            intro h
            exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [1] ∧ LexLE [1] [1])) h)

private theorem k13t7_cover283 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1, 1], HasCheckedCertificate 13 7 ([[1, 1, 2, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover284 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 2], HasCheckedCertificate 13 7 ([[1, 1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover285 : ∀ P ∈ pathPatterns 3 1 [1, 1, 3], HasCheckedCertificate 13 7 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover286 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3, 1], HasCheckedCertificate 13 7 ([[1, 1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover287 : ∀ P ∈ pathPatterns 3 0 [1, 1, 4], HasCheckedCertificate 13 7 ([[1, 1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover289 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 13 7 ([[1, 2], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover290 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 13 7 ([[1, 2], [2]] ++ P) := by
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

private theorem k13t7_cover291 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 13 7 ([[1, 2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover288 : ∀ P ∈ pathPatterns 4 3 [1, 2], HasCheckedCertificate 13 7 ([[1, 2]] ++ P) := by
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
                    fin_cases q
                    · exact by
                        intro h
                        exact False.elim ((by decide : ¬ (LexLE [1, 2] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t7_cover289
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover290
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover291
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover293 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 7 ([[1, 2, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover292 : ∀ P ∈ pathPatterns 3 2 [1, 2, 1], HasCheckedCertificate 13 7 ([[1, 2, 1]] ++ P) := by
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
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover293
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover294 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1, 2], HasCheckedCertificate 13 7 ([[1, 2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover295 : ∀ P ∈ pathPatterns 3 1 [1, 2, 2], HasCheckedCertificate 13 7 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover296 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2, 1], HasCheckedCertificate 13 7 ([[1, 2, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover297 : ∀ P ∈ pathPatterns 3 0 [1, 2, 3], HasCheckedCertificate 13 7 ([[1, 2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover299 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 13 7 ([[1, 3], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover298 : ∀ P ∈ pathPatterns 4 2 [1, 3], HasCheckedCertificate 13 7 ([[1, 3]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 3] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover299
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover300 : ∀ P ∈ pathPatterns 3 1 [1, 3, 1], HasCheckedCertificate 13 7 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover301 : ∀ P ∈ pathPatterns 3 0 [1, 3, 2], HasCheckedCertificate 13 7 ([[1, 3, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover302 : ∀ P ∈ pathPatterns 4 1 [1, 4], HasCheckedCertificate 13 7 ([[1, 4]] ++ P) := by
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

private theorem k13t7_cover303 : ∀ P ∈ pathPatterns 3 0 [1, 4, 1], HasCheckedCertificate 13 7 ([[1, 4, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover304 : ∀ P ∈ pathPatterns 4 0 [1, 5], HasCheckedCertificate 13 7 ([[1, 5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq219 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([1] ++ tail) ∧ LexLE ([1] ++ tail) ([1] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([1] ++ tail).length) (6 - ([1] ++ tail).sum) ([1] ++ tail),
      HasCheckedCertificate 13 7 ([] ++ (([1] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover220
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover256
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover268
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover272
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t7_cover274
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k13t7_cover275
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t7_cover276
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover277
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t7_cover278
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover279
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover280
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover282
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t7_cover283
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover284
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover285
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover286
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover287
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover288
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover292
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
                          constructor
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1, 1] ∧ LexLE [1, 2, 1, 1, 1] [1, 1, 1, 2, 1])) h)
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover294
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover295
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover296
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover297
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover298
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover300
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
                  exact k13t7_cover301
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover302
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover303
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover304
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover307 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 7 ([[2], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t7_cover306 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 13 7 ([[2], [2]] ++ P) := by
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
                exact k13t7_cover307
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover308 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 13 7 ([[2], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover309 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 13 7 ([[2], [3]] ++ P) := by
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

private theorem k13t7_cover310 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 13 7 ([[2], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover305 : ∀ P ∈ pathPatterns 5 4 [2], HasCheckedCertificate 13 7 ([[2]] ++ P) := by
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
                          fin_cases q
                          · exact by
                              intro h
                              exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 1, 1] ∧ LexLE [1, 1, 1, 1] [1, 1, 1, 1])) h)
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [1, 1, 2] ∧ LexLE [1, 1, 2] [2, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2] [1, 2] ∧ LexLE [1, 2] [2, 1])) h)
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [1, 2, 1] ∧ LexLE [1, 2, 1] [1, 2, 1])) h)
                        · intro q
                          exact Fin.elim0 q
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
                exact k13t7_cover306
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [2] [2, 1, 1] ∧ LexLE [2, 1, 1] [1, 1, 2])) h)
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t7_cover308
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t7_cover309
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
                exact k13t7_cover310
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover311 : ∀ P ∈ pathPatterns 2 0 [2, 1, 1, 2], HasCheckedCertificate 13 7 ([[2, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover312 : ∀ P ∈ pathPatterns 3 1 [2, 1, 2], HasCheckedCertificate 13 7 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover313 : ∀ P ∈ pathPatterns 3 0 [2, 1, 3], HasCheckedCertificate 13 7 ([[2, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover314 : ∀ P ∈ pathPatterns 4 2 [2, 2], HasCheckedCertificate 13 7 ([[2, 2]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [2, 2] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [2, 2] [2] ∧ LexLE [2] [2])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover315 : ∀ P ∈ pathPatterns 3 0 [2, 2, 2], HasCheckedCertificate 13 7 ([[2, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover316 : ∀ P ∈ pathPatterns 4 1 [2, 3], HasCheckedCertificate 13 7 ([[2, 3]] ++ P) := by
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

private theorem k13t7_cover317 : ∀ P ∈ pathPatterns 4 0 [2, 4], HasCheckedCertificate 13 7 ([[2, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover319 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 13 7 ([[3], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover318 : ∀ P ∈ pathPatterns 5 3 [3], HasCheckedCertificate 13 7 ([[3]] ++ P) := by
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
                        constructor
                        · exact by
                            intro h
                            exact False.elim ((by decide : ¬ (LexLE [3] [1, 1, 1] ∧ LexLE [1, 1, 1] [1, 1, 1])) h)
                        · intro q
                          exact Fin.elim0 q
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
                exact k13t7_cover319
            · intro q
              exact Fin.elim0 q

private theorem k13t7_cover320 : ∀ P ∈ pathPatterns 4 0 [3, 3], HasCheckedCertificate 13 7 ([[3, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_cover321 : ∀ P ∈ pathPatterns 5 2 [4], HasCheckedCertificate 13 7 ([[4]] ++ P) := by
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

private theorem k13t7_cover322 : ∀ P ∈ pathPatterns 5 1 [5], HasCheckedCertificate 13 7 ([[5]] ++ P) := by
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

private theorem k13t7_cover323 : ∀ P ∈ pathPatterns 5 0 [6], HasCheckedCertificate 13 7 ([[6]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [6] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t7_seq2 : amountSequenceForall 6 6 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (6 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 7 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t7_cover3
  · intro q
    fin_cases q
    · exact k13t7_seq219

    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover305
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
                                constructor
                                · exact by
                                    intro h
                                    exact False.elim ((by decide : ¬ (LexLE [] [2, 1, 1, 1, 1] ∧ LexLE [2, 1, 1, 1, 1] [1, 1, 1, 1, 2])) h)
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t7_cover311
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t7_cover312
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
                        exact k13t7_cover313
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover314
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
                        exact k13t7_cover315
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t7_cover316
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
                  exact k13t7_cover317
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover318
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
                  exact k13t7_cover320
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t7_cover321
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
            exact k13t7_cover322
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
            exact k13t7_cover323
        · intro q
          exact Fin.elim0 q

private theorem k13t7_cover1 : ∀ P ∈ pathPatterns 7 6 [], HasCheckedCertificate 13 7 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t7_seq2


theorem coverage_k13_t7 :
    ∀ P ∈ pathPatterns 7 6, HasCheckedCertificate 13 7 P :=
  k13t7_cover1

private theorem k13t8_cover14 : ∀ P ∈ pathPatterns 0 5 [], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p0, Certificates.k13t8p0_check⟩

private theorem k13t8_cover13 : ∀ P ∈ pathPatterns 1 5 [], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro _
      exact k13t8_cover14

private theorem k13t8_cover15 : ∀ P ∈ pathPatterns 0 4 [1], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p1, Certificates.k13t8p1_check⟩

private theorem k13t8_cover16 : ∀ P ∈ pathPatterns 0 3 [2], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p2, Certificates.k13t8p2_check⟩

private theorem k13t8_cover17 : ∀ P ∈ pathPatterns 0 2 [3], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p3, Certificates.k13t8p3_check⟩

private theorem k13t8_cover18 : ∀ P ∈ pathPatterns 0 1 [4], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p4, Certificates.k13t8p4_check⟩

private theorem k13t8_cover19 : ∀ P ∈ pathPatterns 0 0 [5], HasCheckedCertificate 13 8 ([[], [], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p5, Certificates.k13t8p5_check⟩

private theorem k13t8_cover12 : ∀ P ∈ pathPatterns 2 5 [], HasCheckedCertificate 13 8 ([[], [], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k13t8_cover13
      · intro q
        fin_cases q
        · exact by
            intro _
            exact k13t8_cover15
        · exact by
            intro _
            exact k13t8_cover16
        · exact by
            intro _
            exact k13t8_cover17
        · exact by
            intro _
            exact k13t8_cover18
        · exact by
            intro _
            exact k13t8_cover19

private theorem k13t8_cover20 : ∀ P ∈ pathPatterns 1 4 [1], HasCheckedCertificate 13 8 ([[], [], [], [], [], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover21 : ∀ P ∈ pathPatterns 0 3 [1, 1], HasCheckedCertificate 13 8 ([[], [], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p6, Certificates.k13t8p6_check⟩

private theorem k13t8_cover22 : ∀ P ∈ pathPatterns 0 2 [1, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p7, Certificates.k13t8p7_check⟩

private theorem k13t8_cover23 : ∀ P ∈ pathPatterns 0 1 [1, 3], HasCheckedCertificate 13 8 ([[], [], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p8, Certificates.k13t8p8_check⟩

private theorem k13t8_cover24 : ∀ P ∈ pathPatterns 0 0 [1, 4], HasCheckedCertificate 13 8 ([[], [], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p9, Certificates.k13t8p9_check⟩

private theorem k13t8_cover25 : ∀ P ∈ pathPatterns 1 3 [2], HasCheckedCertificate 13 8 ([[], [], [], [], [], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover26 : ∀ P ∈ pathPatterns 0 1 [2, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p10, Certificates.k13t8p10_check⟩

private theorem k13t8_cover27 : ∀ P ∈ pathPatterns 0 0 [2, 3], HasCheckedCertificate 13 8 ([[], [], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p11, Certificates.k13t8p11_check⟩

private theorem k13t8_cover28 : ∀ P ∈ pathPatterns 1 2 [3], HasCheckedCertificate 13 8 ([[], [], [], [], [], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover29 : ∀ P ∈ pathPatterns 1 1 [4], HasCheckedCertificate 13 8 ([[], [], [], [], [], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover30 : ∀ P ∈ pathPatterns 1 0 [5], HasCheckedCertificate 13 8 ([[], [], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover11 : ∀ P ∈ pathPatterns 3 5 [], HasCheckedCertificate 13 8 ([[], [], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro _
          exact k13t8_cover12
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover20
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t8_cover21
              · exact by
                  intro _
                  exact k13t8_cover22
              · exact by
                  intro _
                  exact k13t8_cover23
              · exact by
                  intro _
                  exact k13t8_cover24
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover25
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t8_cover26
              · exact by
                  intro _
                  exact k13t8_cover27
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover28
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
                exact k13t8_cover29
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [] [4, 1] ∧ LexLE [4, 1] [1, 4])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover30
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover32 : ∀ P ∈ pathPatterns 0 3 [1], HasCheckedCertificate 13 8 ([[], [], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p12, Certificates.k13t8p12_check⟩

private theorem k13t8_cover33 : ∀ P ∈ pathPatterns 0 2 [2], HasCheckedCertificate 13 8 ([[], [], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p13, Certificates.k13t8p13_check⟩

private theorem k13t8_cover34 : ∀ P ∈ pathPatterns 0 1 [3], HasCheckedCertificate 13 8 ([[], [], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p14, Certificates.k13t8p14_check⟩

private theorem k13t8_cover35 : ∀ P ∈ pathPatterns 0 0 [4], HasCheckedCertificate 13 8 ([[], [], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p15, Certificates.k13t8p15_check⟩

private theorem k13t8_cover31 : ∀ P ∈ pathPatterns 2 4 [1], HasCheckedCertificate 13 8 ([[], [], [], [], [1]] ++ P) := by
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
            exact k13t8_cover32
        · exact by
            intro _
            exact k13t8_cover33
        · exact by
            intro _
            exact k13t8_cover34
        · exact by
            intro _
            exact k13t8_cover35

private theorem k13t8_cover36 : ∀ P ∈ pathPatterns 1 3 [1, 1], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover37 : ∀ P ∈ pathPatterns 0 2 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p16, Certificates.k13t8p16_check⟩

private theorem k13t8_cover38 : ∀ P ∈ pathPatterns 0 1 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p17, Certificates.k13t8p17_check⟩

private theorem k13t8_cover39 : ∀ P ∈ pathPatterns 0 0 [1, 1, 3], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p18, Certificates.k13t8p18_check⟩

private theorem k13t8_cover40 : ∀ P ∈ pathPatterns 1 2 [1, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover41 : ∀ P ∈ pathPatterns 0 1 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p19, Certificates.k13t8p19_check⟩

private theorem k13t8_cover42 : ∀ P ∈ pathPatterns 0 0 [1, 2, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p20, Certificates.k13t8p20_check⟩

private theorem k13t8_cover43 : ∀ P ∈ pathPatterns 1 1 [1, 3], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover44 : ∀ P ∈ pathPatterns 0 0 [1, 3, 1], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p21, Certificates.k13t8p21_check⟩

private theorem k13t8_cover45 : ∀ P ∈ pathPatterns 1 0 [1, 4], HasCheckedCertificate 13 8 ([[], [], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover47 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 8 ([[], [], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p22, Certificates.k13t8p22_check⟩

private theorem k13t8_cover48 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 8 ([[], [], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p23, Certificates.k13t8p23_check⟩

private theorem k13t8_cover46 : ∀ P ∈ pathPatterns 2 3 [2], HasCheckedCertificate 13 8 ([[], [], [], [], [2]] ++ P) := by
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
            exact k13t8_cover47
        · exact by
            intro _
            exact k13t8_cover48

private theorem k13t8_cover49 : ∀ P ∈ pathPatterns 0 0 [2, 1, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p24, Certificates.k13t8p24_check⟩

private theorem k13t8_cover50 : ∀ P ∈ pathPatterns 1 1 [2, 2], HasCheckedCertificate 13 8 ([[], [], [], [], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover51 : ∀ P ∈ pathPatterns 1 0 [2, 3], HasCheckedCertificate 13 8 ([[], [], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover52 : ∀ P ∈ pathPatterns 2 2 [3], HasCheckedCertificate 13 8 ([[], [], [], [], [3]] ++ P) := by
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

private theorem k13t8_cover53 : ∀ P ∈ pathPatterns 2 1 [4], HasCheckedCertificate 13 8 ([[], [], [], [], [4]] ++ P) := by
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

private theorem k13t8_cover54 : ∀ P ∈ pathPatterns 2 0 [5], HasCheckedCertificate 13 8 ([[], [], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_seq10 : amountSequenceForall 3 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (3 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 8 ([[], [], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t8_cover11
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover31
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover36
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t8_cover37
                · exact by
                    intro _
                    exact k13t8_cover38
                · exact by
                    intro _
                    exact k13t8_cover39
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover40
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t8_cover41
                · exact by
                    intro _
                    exact k13t8_cover42
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover43
              · intro q
                fin_cases q
                · exact by
                    intro _
                    exact k13t8_cover44
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover45
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover46
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
                    exact k13t8_cover49
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover50
              · intro q
                fin_cases q
                · exact by
                    intro h
                    exact False.elim ((by decide : ¬ (LexLE [] [2, 2, 1] ∧ LexLE [2, 2, 1] [1, 2, 2])) h)
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover51
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover52
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
            exact k13t8_cover53
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
            exact k13t8_cover54
        · intro q
          exact Fin.elim0 q

private theorem k13t8_cover9 : ∀ P ∈ pathPatterns 4 5 [], HasCheckedCertificate 13 8 ([[], [], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t8_seq10


private theorem k13t8_cover56 : ∀ P ∈ pathPatterns 1 3 [1], HasCheckedCertificate 13 8 ([[], [], [], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover57 : ∀ P ∈ pathPatterns 0 2 [1, 1], HasCheckedCertificate 13 8 ([[], [], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p25, Certificates.k13t8p25_check⟩

private theorem k13t8_cover58 : ∀ P ∈ pathPatterns 0 1 [1, 2], HasCheckedCertificate 13 8 ([[], [], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p26, Certificates.k13t8p26_check⟩

private theorem k13t8_cover59 : ∀ P ∈ pathPatterns 0 0 [1, 3], HasCheckedCertificate 13 8 ([[], [], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p27, Certificates.k13t8p27_check⟩

private theorem k13t8_cover60 : ∀ P ∈ pathPatterns 1 2 [2], HasCheckedCertificate 13 8 ([[], [], [], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover61 : ∀ P ∈ pathPatterns 0 0 [2, 2], HasCheckedCertificate 13 8 ([[], [], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p28, Certificates.k13t8p28_check⟩

private theorem k13t8_cover62 : ∀ P ∈ pathPatterns 1 1 [3], HasCheckedCertificate 13 8 ([[], [], [], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover63 : ∀ P ∈ pathPatterns 1 0 [4], HasCheckedCertificate 13 8 ([[], [], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover55 : ∀ P ∈ pathPatterns 3 4 [1], HasCheckedCertificate 13 8 ([[], [], [], [1]] ++ P) := by
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
                exact k13t8_cover56
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t8_cover57
              · exact by
                  intro _
                  exact k13t8_cover58
              · exact by
                  intro _
                  exact k13t8_cover59
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover60
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
              · exact by
                  intro _
                  exact k13t8_cover61
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover62
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [3, 1] ∧ LexLE [3, 1] [1, 3])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover63
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover65 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 8 ([[], [], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p29, Certificates.k13t8p29_check⟩

private theorem k13t8_cover66 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 8 ([[], [], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p30, Certificates.k13t8p30_check⟩

private theorem k13t8_cover64 : ∀ P ∈ pathPatterns 2 3 [1, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 1]] ++ P) := by
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
            exact k13t8_cover65
        · exact by
            intro _
            exact k13t8_cover66

private theorem k13t8_cover67 : ∀ P ∈ pathPatterns 1 2 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover68 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p31, Certificates.k13t8p31_check⟩

private theorem k13t8_cover69 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p32, Certificates.k13t8p32_check⟩

private theorem k13t8_cover70 : ∀ P ∈ pathPatterns 1 1 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover71 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p33, Certificates.k13t8p33_check⟩

private theorem k13t8_cover72 : ∀ P ∈ pathPatterns 1 0 [1, 1, 3], HasCheckedCertificate 13 8 ([[], [], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover74 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 8 ([[], [], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p34, Certificates.k13t8p34_check⟩

private theorem k13t8_cover73 : ∀ P ∈ pathPatterns 2 2 [1, 2], HasCheckedCertificate 13 8 ([[], [], [], [1, 2]] ++ P) := by
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
            exact k13t8_cover74

private theorem k13t8_cover75 : ∀ P ∈ pathPatterns 1 1 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover76 : ∀ P ∈ pathPatterns 1 0 [1, 2, 2], HasCheckedCertificate 13 8 ([[], [], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover77 : ∀ P ∈ pathPatterns 2 1 [1, 3], HasCheckedCertificate 13 8 ([[], [], [], [1, 3]] ++ P) := by
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

private theorem k13t8_cover78 : ∀ P ∈ pathPatterns 1 0 [1, 3, 1], HasCheckedCertificate 13 8 ([[], [], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover79 : ∀ P ∈ pathPatterns 2 0 [1, 4], HasCheckedCertificate 13 8 ([[], [], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover81 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 8 ([[], [], [], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover82 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 8 ([[], [], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover80 : ∀ P ∈ pathPatterns 3 3 [2], HasCheckedCertificate 13 8 ([[], [], [], [2]] ++ P) := by
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
                exact k13t8_cover81
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [2] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover82
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover83 : ∀ P ∈ pathPatterns 1 0 [2, 1, 2], HasCheckedCertificate 13 8 ([[], [], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover84 : ∀ P ∈ pathPatterns 2 1 [2, 2], HasCheckedCertificate 13 8 ([[], [], [], [2, 2]] ++ P) := by
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

private theorem k13t8_cover85 : ∀ P ∈ pathPatterns 2 0 [2, 3], HasCheckedCertificate 13 8 ([[], [], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover86 : ∀ P ∈ pathPatterns 3 2 [3], HasCheckedCertificate 13 8 ([[], [], [], [3]] ++ P) := by
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

private theorem k13t8_cover87 : ∀ P ∈ pathPatterns 3 1 [4], HasCheckedCertificate 13 8 ([[], [], [], [4]] ++ P) := by
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

private theorem k13t8_cover88 : ∀ P ∈ pathPatterns 3 0 [5], HasCheckedCertificate 13 8 ([[], [], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_seq8 : amountSequenceForall 4 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (4 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 8 ([[], [], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t8_cover9
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover55
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover64
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover67
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t8_cover68
                      · exact by
                          intro _
                          exact k13t8_cover69
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover70
                    · intro q
                      fin_cases q
                      · exact by
                          intro _
                          exact k13t8_cover71
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover72
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover73
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover75
                    · intro q
                      fin_cases q
                      · exact by
                          intro h
                          exact False.elim ((by decide : ¬ (LexLE [] [1, 2, 1, 1] ∧ LexLE [1, 2, 1, 1] [1, 1, 2, 1])) h)
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover76
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover77
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover78
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover79
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover80
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
                        exact k13t8_cover83
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover84
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
                  exact k13t8_cover85
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover86
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
            exact k13t8_cover87
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
            exact k13t8_cover88
        · intro q
          exact Fin.elim0 q

private theorem k13t8_cover7 : ∀ P ∈ pathPatterns 5 5 [], HasCheckedCertificate 13 8 ([[], [], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t8_seq8


private theorem k13t8_cover91 : ∀ P ∈ pathPatterns 0 2 [1], HasCheckedCertificate 13 8 ([[], [], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p35, Certificates.k13t8p35_check⟩

private theorem k13t8_cover92 : ∀ P ∈ pathPatterns 0 1 [2], HasCheckedCertificate 13 8 ([[], [], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p36, Certificates.k13t8p36_check⟩

private theorem k13t8_cover93 : ∀ P ∈ pathPatterns 0 0 [3], HasCheckedCertificate 13 8 ([[], [], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p37, Certificates.k13t8p37_check⟩

private theorem k13t8_cover90 : ∀ P ∈ pathPatterns 2 3 [1], HasCheckedCertificate 13 8 ([[], [], [1], [1]] ++ P) := by
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
            exact k13t8_cover91
        · exact by
            intro _
            exact k13t8_cover92
        · exact by
            intro _
            exact k13t8_cover93

private theorem k13t8_cover94 : ∀ P ∈ pathPatterns 1 2 [1, 1], HasCheckedCertificate 13 8 ([[], [], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover95 : ∀ P ∈ pathPatterns 0 1 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p38, Certificates.k13t8p38_check⟩

private theorem k13t8_cover96 : ∀ P ∈ pathPatterns 0 0 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p39, Certificates.k13t8p39_check⟩

private theorem k13t8_cover97 : ∀ P ∈ pathPatterns 1 1 [1, 2], HasCheckedCertificate 13 8 ([[], [], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover98 : ∀ P ∈ pathPatterns 0 0 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p40, Certificates.k13t8p40_check⟩

private theorem k13t8_cover99 : ∀ P ∈ pathPatterns 1 0 [1, 3], HasCheckedCertificate 13 8 ([[], [], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover101 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 8 ([[], [], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p41, Certificates.k13t8p41_check⟩

private theorem k13t8_cover100 : ∀ P ∈ pathPatterns 2 2 [2], HasCheckedCertificate 13 8 ([[], [], [1], [2]] ++ P) := by
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
            exact k13t8_cover101

private theorem k13t8_cover102 : ∀ P ∈ pathPatterns 1 0 [2, 2], HasCheckedCertificate 13 8 ([[], [], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover103 : ∀ P ∈ pathPatterns 2 1 [3], HasCheckedCertificate 13 8 ([[], [], [1], [3]] ++ P) := by
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

private theorem k13t8_cover104 : ∀ P ∈ pathPatterns 2 0 [4], HasCheckedCertificate 13 8 ([[], [], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover89 : ∀ P ∈ pathPatterns 4 4 [1], HasCheckedCertificate 13 8 ([[], [], [1]] ++ P) := by
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
                exact k13t8_cover90
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover94
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t8_cover95
                    · exact by
                        intro _
                        exact k13t8_cover96
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover97
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t8_cover98
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover99
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover100
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
                      exact k13t8_cover102
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover103
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
                exact k13t8_cover104
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover106 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p42, Certificates.k13t8p42_check⟩

private theorem k13t8_cover107 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 13 8 ([[], [], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p43, Certificates.k13t8p43_check⟩

private theorem k13t8_cover108 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 8 ([[], [], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover109 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 8 ([[], [], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover105 : ∀ P ∈ pathPatterns 3 3 [1, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1]] ++ P) := by
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
                  exact k13t8_cover106
              · exact by
                  intro _
                  exact k13t8_cover107
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover108
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1, 1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover109
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover111 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 8 ([[], [], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p44, Certificates.k13t8p44_check⟩

private theorem k13t8_cover110 : ∀ P ∈ pathPatterns 2 2 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1, 1]] ++ P) := by
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
            exact k13t8_cover111

private theorem k13t8_cover112 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover113 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p45, Certificates.k13t8p45_check⟩

private theorem k13t8_cover114 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover115 : ∀ P ∈ pathPatterns 2 1 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [], [1, 1, 2]] ++ P) := by
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

private theorem k13t8_cover116 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover117 : ∀ P ∈ pathPatterns 2 0 [1, 1, 3], HasCheckedCertificate 13 8 ([[], [], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover119 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 8 ([[], [], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover118 : ∀ P ∈ pathPatterns 3 2 [1, 2], HasCheckedCertificate 13 8 ([[], [], [1, 2]] ++ P) := by
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
                exact k13t8_cover119
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover120 : ∀ P ∈ pathPatterns 2 1 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [], [1, 2, 1]] ++ P) := by
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

private theorem k13t8_cover121 : ∀ P ∈ pathPatterns 2 0 [1, 2, 2], HasCheckedCertificate 13 8 ([[], [], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover122 : ∀ P ∈ pathPatterns 3 1 [1, 3], HasCheckedCertificate 13 8 ([[], [], [1, 3]] ++ P) := by
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

private theorem k13t8_cover123 : ∀ P ∈ pathPatterns 2 0 [1, 3, 1], HasCheckedCertificate 13 8 ([[], [], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover124 : ∀ P ∈ pathPatterns 3 0 [1, 4], HasCheckedCertificate 13 8 ([[], [], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover126 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 13 8 ([[], [], [2], [2]] ++ P) := by
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

private theorem k13t8_cover127 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 13 8 ([[], [], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover125 : ∀ P ∈ pathPatterns 4 3 [2], HasCheckedCertificate 13 8 ([[], [], [2]] ++ P) := by
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
                exact k13t8_cover126
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
                exact k13t8_cover127
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover128 : ∀ P ∈ pathPatterns 2 0 [2, 1, 2], HasCheckedCertificate 13 8 ([[], [], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover129 : ∀ P ∈ pathPatterns 3 1 [2, 2], HasCheckedCertificate 13 8 ([[], [], [2, 2]] ++ P) := by
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

private theorem k13t8_cover130 : ∀ P ∈ pathPatterns 3 0 [2, 3], HasCheckedCertificate 13 8 ([[], [], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover131 : ∀ P ∈ pathPatterns 4 2 [3], HasCheckedCertificate 13 8 ([[], [], [3]] ++ P) := by
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

private theorem k13t8_cover132 : ∀ P ∈ pathPatterns 4 1 [4], HasCheckedCertificate 13 8 ([[], [], [4]] ++ P) := by
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

private theorem k13t8_cover133 : ∀ P ∈ pathPatterns 4 0 [5], HasCheckedCertificate 13 8 ([[], [], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_seq6 : amountSequenceForall 5 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (5 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 8 ([[], []] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t8_cover7
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover89
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover105
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover110
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover112
                          · intro q
                            fin_cases q
                            · exact by
                                intro _
                                exact k13t8_cover113
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover114
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover115
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover116
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover117
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover118
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover120
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
                        exact k13t8_cover121
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover122
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover123
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover124
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover125
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
                        exact k13t8_cover128
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover129
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
                  exact k13t8_cover130
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover131
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
            exact k13t8_cover132
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
            exact k13t8_cover133
        · intro q
          exact Fin.elim0 q

private theorem k13t8_cover5 : ∀ P ∈ pathPatterns 6 5 [], HasCheckedCertificate 13 8 ([[], []] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t8_seq6


private theorem k13t8_cover136 : ∀ P ∈ pathPatterns 1 2 [1], HasCheckedCertificate 13 8 ([[], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover137 : ∀ P ∈ pathPatterns 0 1 [1, 1], HasCheckedCertificate 13 8 ([[], [1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p46, Certificates.k13t8p46_check⟩

private theorem k13t8_cover138 : ∀ P ∈ pathPatterns 0 0 [1, 2], HasCheckedCertificate 13 8 ([[], [1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p47, Certificates.k13t8p47_check⟩

private theorem k13t8_cover139 : ∀ P ∈ pathPatterns 1 1 [2], HasCheckedCertificate 13 8 ([[], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover140 : ∀ P ∈ pathPatterns 1 0 [3], HasCheckedCertificate 13 8 ([[], [1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover135 : ∀ P ∈ pathPatterns 3 3 [1], HasCheckedCertificate 13 8 ([[], [1], [1]] ++ P) := by
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
                exact k13t8_cover136
            · intro q
              fin_cases q
              · exact by
                  intro _
                  exact k13t8_cover137
              · exact by
                  intro _
                  exact k13t8_cover138
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover139
            · intro q
              fin_cases q
              · exact by
                  intro h
                  exact False.elim ((by decide : ¬ (LexLE [1] [2, 1] ∧ LexLE [2, 1] [1, 2])) h)
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover140
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover142 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 8 ([[], [1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p48, Certificates.k13t8p48_check⟩

private theorem k13t8_cover141 : ∀ P ∈ pathPatterns 2 2 [1, 1], HasCheckedCertificate 13 8 ([[], [1], [1, 1]] ++ P) := by
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
            exact k13t8_cover142

private theorem k13t8_cover143 : ∀ P ∈ pathPatterns 1 1 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover144 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p49, Certificates.k13t8p49_check⟩

private theorem k13t8_cover145 : ∀ P ∈ pathPatterns 1 0 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover146 : ∀ P ∈ pathPatterns 2 1 [1, 2], HasCheckedCertificate 13 8 ([[], [1], [1, 2]] ++ P) := by
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

private theorem k13t8_cover147 : ∀ P ∈ pathPatterns 1 0 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover148 : ∀ P ∈ pathPatterns 2 0 [1, 3], HasCheckedCertificate 13 8 ([[], [1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover150 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 8 ([[], [1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover149 : ∀ P ∈ pathPatterns 3 2 [2], HasCheckedCertificate 13 8 ([[], [1], [2]] ++ P) := by
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
                exact k13t8_cover150
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover151 : ∀ P ∈ pathPatterns 2 0 [2, 2], HasCheckedCertificate 13 8 ([[], [1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover152 : ∀ P ∈ pathPatterns 3 1 [3], HasCheckedCertificate 13 8 ([[], [1], [3]] ++ P) := by
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

private theorem k13t8_cover153 : ∀ P ∈ pathPatterns 3 0 [4], HasCheckedCertificate 13 8 ([[], [1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover134 : ∀ P ∈ pathPatterns 5 4 [1], HasCheckedCertificate 13 8 ([[], [1]] ++ P) := by
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
                exact k13t8_cover135
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover141
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover143
                        · intro q
                          fin_cases q
                          · exact by
                              intro _
                              exact k13t8_cover144
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover145
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover146
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover147
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover148
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover149
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
                      exact k13t8_cover151
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover152
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
                exact k13t8_cover153
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover155 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 13 8 ([[], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover156 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p50, Certificates.k13t8p50_check⟩

private theorem k13t8_cover157 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 13 8 ([[], [1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover158 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 13 8 ([[], [1, 1], [2]] ++ P) := by
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

private theorem k13t8_cover159 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 13 8 ([[], [1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover154 : ∀ P ∈ pathPatterns 4 3 [1, 1], HasCheckedCertificate 13 8 ([[], [1, 1]] ++ P) := by
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
                      exact k13t8_cover155
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t8_cover156
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover157
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover158
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
                exact k13t8_cover159
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover161 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 8 ([[], [1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover160 : ∀ P ∈ pathPatterns 3 2 [1, 1, 1], HasCheckedCertificate 13 8 ([[], [1, 1, 1]] ++ P) := by
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
                exact k13t8_cover161
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover162 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [1, 1, 1, 1]] ++ P) := by
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

private theorem k13t8_cover163 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1, 1], HasCheckedCertificate 13 8 ([[], [1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover164 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 2], HasCheckedCertificate 13 8 ([[], [1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover165 : ∀ P ∈ pathPatterns 3 1 [1, 1, 2], HasCheckedCertificate 13 8 ([[], [1, 1, 2]] ++ P) := by
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

private theorem k13t8_cover166 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2, 1], HasCheckedCertificate 13 8 ([[], [1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover167 : ∀ P ∈ pathPatterns 3 0 [1, 1, 3], HasCheckedCertificate 13 8 ([[], [1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover169 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 13 8 ([[], [1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover168 : ∀ P ∈ pathPatterns 4 2 [1, 2], HasCheckedCertificate 13 8 ([[], [1, 2]] ++ P) := by
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
                exact k13t8_cover169
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover170 : ∀ P ∈ pathPatterns 3 1 [1, 2, 1], HasCheckedCertificate 13 8 ([[], [1, 2, 1]] ++ P) := by
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

private theorem k13t8_cover171 : ∀ P ∈ pathPatterns 3 0 [1, 2, 2], HasCheckedCertificate 13 8 ([[], [1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover172 : ∀ P ∈ pathPatterns 4 1 [1, 3], HasCheckedCertificate 13 8 ([[], [1, 3]] ++ P) := by
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

private theorem k13t8_cover173 : ∀ P ∈ pathPatterns 3 0 [1, 3, 1], HasCheckedCertificate 13 8 ([[], [1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover174 : ∀ P ∈ pathPatterns 4 0 [1, 4], HasCheckedCertificate 13 8 ([[], [1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover176 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 13 8 ([[], [2], [2]] ++ P) := by
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

private theorem k13t8_cover177 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 13 8 ([[], [2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover175 : ∀ P ∈ pathPatterns 5 3 [2], HasCheckedCertificate 13 8 ([[], [2]] ++ P) := by
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
                exact k13t8_cover176
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
                exact k13t8_cover177
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover178 : ∀ P ∈ pathPatterns 3 0 [2, 1, 2], HasCheckedCertificate 13 8 ([[], [2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover179 : ∀ P ∈ pathPatterns 4 1 [2, 2], HasCheckedCertificate 13 8 ([[], [2, 2]] ++ P) := by
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

private theorem k13t8_cover180 : ∀ P ∈ pathPatterns 4 0 [2, 3], HasCheckedCertificate 13 8 ([[], [2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover181 : ∀ P ∈ pathPatterns 5 2 [3], HasCheckedCertificate 13 8 ([[], [3]] ++ P) := by
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

private theorem k13t8_cover182 : ∀ P ∈ pathPatterns 5 1 [4], HasCheckedCertificate 13 8 ([[], [4]] ++ P) := by
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

private theorem k13t8_cover183 : ∀ P ∈ pathPatterns 5 0 [5], HasCheckedCertificate 13 8 ([[], [5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_seq4 : amountSequenceForall 6 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (6 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 8 ([[]] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t8_cover5
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover134
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover154
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover160
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover162
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro _
                                    exact k13t8_cover163
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover164
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover165
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover166
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover167
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover168
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover170
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
                        exact k13t8_cover171
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover172
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover173
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover174
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover175
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
                        exact k13t8_cover178
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover179
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
                  exact k13t8_cover180
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover181
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
            exact k13t8_cover182
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
            exact k13t8_cover183
        · intro q
          exact Fin.elim0 q

private theorem k13t8_cover3 : ∀ P ∈ pathPatterns 7 5 [], HasCheckedCertificate 13 8 ([[]] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t8_seq4


private theorem k13t8_cover187 : ∀ P ∈ pathPatterns 0 1 [1], HasCheckedCertificate 13 8 ([[1], [1], [1], [1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p51, Certificates.k13t8p51_check⟩

private theorem k13t8_cover188 : ∀ P ∈ pathPatterns 0 0 [2], HasCheckedCertificate 13 8 ([[1], [1], [1], [2]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p52, Certificates.k13t8p52_check⟩

private theorem k13t8_cover186 : ∀ P ∈ pathPatterns 2 2 [1], HasCheckedCertificate 13 8 ([[1], [1], [1]] ++ P) := by
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
            exact k13t8_cover187
        · exact by
            intro _
            exact k13t8_cover188

private theorem k13t8_cover189 : ∀ P ∈ pathPatterns 1 1 [1, 1], HasCheckedCertificate 13 8 ([[1], [1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover190 : ∀ P ∈ pathPatterns 0 0 [1, 1, 1], HasCheckedCertificate 13 8 ([[1], [1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p53, Certificates.k13t8p53_check⟩

private theorem k13t8_cover191 : ∀ P ∈ pathPatterns 1 0 [1, 2], HasCheckedCertificate 13 8 ([[1], [1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover192 : ∀ P ∈ pathPatterns 2 1 [2], HasCheckedCertificate 13 8 ([[1], [1], [2]] ++ P) := by
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

private theorem k13t8_cover193 : ∀ P ∈ pathPatterns 2 0 [3], HasCheckedCertificate 13 8 ([[1], [1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover185 : ∀ P ∈ pathPatterns 4 3 [1], HasCheckedCertificate 13 8 ([[1], [1]] ++ P) := by
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
                exact k13t8_cover186
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover189
                  · intro q
                    fin_cases q
                    · exact by
                        intro _
                        exact k13t8_cover190
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover191
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover192
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
                exact k13t8_cover193
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover195 : ∀ P ∈ pathPatterns 0 0 [1, 1], HasCheckedCertificate 13 8 ([[1], [1, 1], [1, 1]] ++ P) := by
  apply pathPatterns_forall_zero
  exact ⟨_, Certificates.k13t8p54, Certificates.k13t8p54_check⟩

private theorem k13t8_cover196 : ∀ P ∈ pathPatterns 1 0 [2], HasCheckedCertificate 13 8 ([[1], [1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover194 : ∀ P ∈ pathPatterns 3 2 [1, 1], HasCheckedCertificate 13 8 ([[1], [1, 1]] ++ P) := by
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
                  exact k13t8_cover195
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover196
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover197 : ∀ P ∈ pathPatterns 2 1 [1, 1, 1], HasCheckedCertificate 13 8 ([[1], [1, 1, 1]] ++ P) := by
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

private theorem k13t8_cover198 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[1], [1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover199 : ∀ P ∈ pathPatterns 2 0 [1, 1, 2], HasCheckedCertificate 13 8 ([[1], [1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover200 : ∀ P ∈ pathPatterns 3 1 [1, 2], HasCheckedCertificate 13 8 ([[1], [1, 2]] ++ P) := by
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

private theorem k13t8_cover201 : ∀ P ∈ pathPatterns 2 0 [1, 2, 1], HasCheckedCertificate 13 8 ([[1], [1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover202 : ∀ P ∈ pathPatterns 3 0 [1, 3], HasCheckedCertificate 13 8 ([[1], [1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover204 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 13 8 ([[1], [2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover203 : ∀ P ∈ pathPatterns 4 2 [2], HasCheckedCertificate 13 8 ([[1], [2]] ++ P) := by
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
                exact k13t8_cover204
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover205 : ∀ P ∈ pathPatterns 3 0 [2, 2], HasCheckedCertificate 13 8 ([[1], [2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover206 : ∀ P ∈ pathPatterns 4 1 [3], HasCheckedCertificate 13 8 ([[1], [3]] ++ P) := by
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

private theorem k13t8_cover207 : ∀ P ∈ pathPatterns 4 0 [4], HasCheckedCertificate 13 8 ([[1], [4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover184 : ∀ P ∈ pathPatterns 6 4 [1], HasCheckedCertificate 13 8 ([[1]] ++ P) := by
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
                exact k13t8_cover185
            · intro q
              fin_cases q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover194
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover197
                        · intro q
                          fin_cases q
                          · exact by
                              constructor
                              · exact by
                                  intro _
                                  exact k13t8_cover198
                              · intro q
                                exact Fin.elim0 q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover199
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover200
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover201
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover202
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover203
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
                      exact k13t8_cover205
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover206
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
                exact k13t8_cover207
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover209 : ∀ P ∈ pathPatterns 2 1 [1, 1], HasCheckedCertificate 13 8 ([[1, 1], [1, 1]] ++ P) := by
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

private theorem k13t8_cover210 : ∀ P ∈ pathPatterns 1 0 [1, 1, 1], HasCheckedCertificate 13 8 ([[1, 1], [1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      intro h
      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [] ∧ LexLE [] [])) h)

private theorem k13t8_cover211 : ∀ P ∈ pathPatterns 2 0 [1, 2], HasCheckedCertificate 13 8 ([[1, 1], [1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover212 : ∀ P ∈ pathPatterns 3 1 [2], HasCheckedCertificate 13 8 ([[1, 1], [2]] ++ P) := by
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

private theorem k13t8_cover213 : ∀ P ∈ pathPatterns 3 0 [3], HasCheckedCertificate 13 8 ([[1, 1], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover208 : ∀ P ∈ pathPatterns 5 3 [1, 1], HasCheckedCertificate 13 8 ([[1, 1]] ++ P) := by
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
                      exact k13t8_cover209
                  · intro q
                    fin_cases q
                    · exact by
                        constructor
                        · exact by
                            intro _
                            exact k13t8_cover210
                        · intro q
                          exact Fin.elim0 q
              · exact by
                  constructor
                  · exact by
                      intro _
                      exact k13t8_cover211
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover212
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
                exact k13t8_cover213
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover215 : ∀ P ∈ pathPatterns 2 0 [2], HasCheckedCertificate 13 8 ([[1, 1, 1], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover214 : ∀ P ∈ pathPatterns 4 2 [1, 1, 1], HasCheckedCertificate 13 8 ([[1, 1, 1]] ++ P) := by
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
                  constructor
                  · exact by
                      intro h
                      exact False.elim ((by decide : ¬ (LexLE [1, 1, 1] [1, 1] ∧ LexLE [1, 1] [1, 1])) h)
                  · intro q
                    exact Fin.elim0 q
        · exact by
            constructor
            · exact by
                intro _
                exact k13t8_cover215
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover216 : ∀ P ∈ pathPatterns 3 1 [1, 1, 1, 1], HasCheckedCertificate 13 8 ([[1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        fin_cases q
        · exact by
            constructor
            · exact by
                intro h
                exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1] [1] ∧ LexLE [1] [1])) h)
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover217 : ∀ P ∈ pathPatterns 2 0 [1, 1, 1, 1, 1], HasCheckedCertificate 13 8 ([[1, 1, 1, 1, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 1, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover218 : ∀ P ∈ pathPatterns 3 0 [1, 1, 1, 2], HasCheckedCertificate 13 8 ([[1, 1, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover219 : ∀ P ∈ pathPatterns 4 1 [1, 1, 2], HasCheckedCertificate 13 8 ([[1, 1, 2]] ++ P) := by
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

private theorem k13t8_cover220 : ∀ P ∈ pathPatterns 3 0 [1, 1, 2, 1], HasCheckedCertificate 13 8 ([[1, 1, 2, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 2, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover221 : ∀ P ∈ pathPatterns 4 0 [1, 1, 3], HasCheckedCertificate 13 8 ([[1, 1, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 1, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover223 : ∀ P ∈ pathPatterns 3 0 [2], HasCheckedCertificate 13 8 ([[1, 2], [2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover222 : ∀ P ∈ pathPatterns 5 2 [1, 2], HasCheckedCertificate 13 8 ([[1, 2]] ++ P) := by
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
                exact k13t8_cover223
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover224 : ∀ P ∈ pathPatterns 4 1 [1, 2, 1], HasCheckedCertificate 13 8 ([[1, 2, 1]] ++ P) := by
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

private theorem k13t8_cover225 : ∀ P ∈ pathPatterns 4 0 [1, 2, 2], HasCheckedCertificate 13 8 ([[1, 2, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 2, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover226 : ∀ P ∈ pathPatterns 5 1 [1, 3], HasCheckedCertificate 13 8 ([[1, 3]] ++ P) := by
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

private theorem k13t8_cover227 : ∀ P ∈ pathPatterns 4 0 [1, 3, 1], HasCheckedCertificate 13 8 ([[1, 3, 1]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 3, 1] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover228 : ∀ P ∈ pathPatterns 5 0 [1, 4], HasCheckedCertificate 13 8 ([[1, 4]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [1, 4] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover230 : ∀ P ∈ pathPatterns 4 1 [2], HasCheckedCertificate 13 8 ([[2], [2]] ++ P) := by
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

private theorem k13t8_cover231 : ∀ P ∈ pathPatterns 4 0 [3], HasCheckedCertificate 13 8 ([[2], [3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover229 : ∀ P ∈ pathPatterns 6 3 [2], HasCheckedCertificate 13 8 ([[2]] ++ P) := by
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
                exact k13t8_cover230
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
                exact k13t8_cover231
            · intro q
              exact Fin.elim0 q

private theorem k13t8_cover232 : ∀ P ∈ pathPatterns 4 0 [2, 1, 2], HasCheckedCertificate 13 8 ([[2, 1, 2]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 1, 2] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover233 : ∀ P ∈ pathPatterns 5 1 [2, 2], HasCheckedCertificate 13 8 ([[2, 2]] ++ P) := by
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

private theorem k13t8_cover234 : ∀ P ∈ pathPatterns 5 0 [2, 3], HasCheckedCertificate 13 8 ([[2, 3]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [2, 3] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_cover235 : ∀ P ∈ pathPatterns 6 2 [3], HasCheckedCertificate 13 8 ([[3]] ++ P) := by
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

private theorem k13t8_cover236 : ∀ P ∈ pathPatterns 6 1 [4], HasCheckedCertificate 13 8 ([[4]] ++ P) := by
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

private theorem k13t8_cover237 : ∀ P ∈ pathPatterns 6 0 [5], HasCheckedCertificate 13 8 ([[5]] ++ P) := by
  apply pathPatterns_forall_step
  exact by
      constructor
      · exact by
          intro h
          exact False.elim ((by decide : ¬ (LexLE [5] [] ∧ LexLE [] [])) h)
      · intro q
        exact Fin.elim0 q

private theorem k13t8_seq2 : amountSequenceForall 7 5 (fun tail =>
    (LexLE [] ([] ++ tail) ∧ LexLE ([] ++ tail) ([] ++ tail).reverse) →
    ∀ P ∈ pathPatterns (7 - ([] ++ tail).length) (5 - ([] ++ tail).sum) ([] ++ tail),
      HasCheckedCertificate 13 8 ([] ++ (([] ++ tail) :: P))) :=
by
  constructor
  · exact by
      intro _
      exact k13t8_cover3
  · intro q
    fin_cases q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover184
        · intro q
          fin_cases q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover208
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover214
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover216
                          · intro q
                            fin_cases q
                            · exact by
                                constructor
                                · exact by
                                    intro _
                                    exact k13t8_cover217
                                · intro q
                                  exact Fin.elim0 q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover218
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover219
                    · intro q
                      fin_cases q
                      · exact by
                          constructor
                          · exact by
                              intro _
                              exact k13t8_cover220
                          · intro q
                            exact Fin.elim0 q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover221
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover222
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover224
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
                        exact k13t8_cover225
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover226
              · intro q
                fin_cases q
                · exact by
                    constructor
                    · exact by
                        intro _
                        exact k13t8_cover227
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover228
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover229
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
                        exact k13t8_cover232
                    · intro q
                      exact Fin.elim0 q
          · exact by
              constructor
              · exact by
                  intro _
                  exact k13t8_cover233
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
                  exact k13t8_cover234
              · intro q
                exact Fin.elim0 q
    · exact by
        constructor
        · exact by
            intro _
            exact k13t8_cover235
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
            exact k13t8_cover236
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
            exact k13t8_cover237
        · intro q
          exact Fin.elim0 q

private theorem k13t8_cover1 : ∀ P ∈ pathPatterns 8 5 [], HasCheckedCertificate 13 8 ([] ++ P) := by
  apply pathPatterns_forall_step
  exact k13t8_seq2


theorem coverage_k13_t8 :
    ∀ P ∈ pathPatterns 8 5, HasCheckedCertificate 13 8 P :=
  k13t8_cover1

end CycleClique.Construction.CertifiedCoverage

end OAI
