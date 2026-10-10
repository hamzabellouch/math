import OAI.Geometry.HeilbronnTriangle.PairingMoment
import OAI.Geometry.HeilbronnTriangle.PrimitiveNormal
import OAI.Geometry.HeilbronnTriangle.LatticePacking
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice
import OAI.Geometry.HeilbronnTriangle.AffineShellCount
import OAI.Geometry.HeilbronnTriangle.ExactPlaneCovolume

namespace OAI


namespace Problem355.ZeroAffineShell

open scoped BigOperators Matrix
open PairingDivisor PrimitiveNormal

theorem pairing_moment_euclidean_shell
    (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L) :
    ∑ x ∈ S, (pairingDivisor L x : ℝ) ^ 3 ≤
      1024 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  have hbox : ∀ x ∈ S, ∀ i, -((2 * R : ℕ) : ℤ) ≤ x i ∧
      x i ≤ ((2 * R : ℕ) : ℤ) := by
    intro x hx i
    have hcoord : |(x i : ℝ)| ≤ ‖toEuclidean x‖ := by
      change ‖(toEuclidean x).ofLp i‖ ≤ ‖toEuclidean x‖
      exact PiLp.norm_apply_le _ _
    have hbound : |(x i : ℝ)| ≤ (2 * R : ℕ) := by
      push_cast
      exact hcoord.trans (hnorm x hx).le
    have hz : |x i| ≤ ((2 * R : ℕ) : ℤ) := by exact_mod_cast hbound
    exact abs_le.mp hz
  have hm := LatticeMoment.pairing_divisor_moment_of_diagonal_form
    S L C B (2 * R) b e k hB hR hek P Q hC hbox
    (fun x hx => (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx))
    hcontain hrows
  convert hm using 1
  push_cast
  ring

private lemma row_cubic_constant (W N J : ℝ) :
    W * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 =
      (W * (144 * Real.pi) ^ 3 * N ^ 6) / J ^ 3 := by
  ring

theorem weighted_spanning_triples_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (T : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ a ∈ T, W a ≤ W₀)
    (hshort : ∀ a ∈ T, ∀ i, ‖(a i : E)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)]) :
    (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
      ZLattice.covolume L ^ 3 := by
  have hc := LatticePacking.plane_spanning_triples_card_le hdim L T (4 * N)
    (by positivity) hshort hpair
  generalize hJ : ZLattice.covolume L MeasureTheory.volume = J at hc ⊢
  calc
    (∑ a ∈ T, W a) ≤ ∑ _a ∈ T, W₀ := Finset.sum_le_sum hW
    _ = W₀ * (T.card : ℝ) := by simp [mul_comm]
    _ ≤ W₀ * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 :=
      mul_le_mul_of_nonneg_left hc hW₀
    _ = _ := row_cubic_constant W₀ N (J)

theorem weighted_lattice_fibre_le
    (x z : Fin 3 → ℤ) (hz : dotProduct x z = 1)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L)
    (T : Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ a ∈ T, W a ≤ W₀)
    (hshort : ∀ a ∈ T, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ T, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)]) :
    (∑ a ∈ T, W a) ≤ (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) /
      ZLattice.covolume (IntegralPlaneLattice.latticeIn x L) ^ 3 := by
  let := IntegralPlaneLattice.latticeIn_isZLattice x z hz L
    (E : ℤ) (by exact_mod_cast Nat.ne_of_gt hE)
    (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
  exact weighted_spanning_triples_le (IntegralPlaneLattice.plane_finrank x z hz)
    (IntegralPlaneLattice.latticeIn x L) T W N W₀ hN hW₀ hW hshort hpair

theorem canonical_pairing_covolume
    (x : Fin 3 → ℤ) (hx : IsPrimitive x)
    (L : Submodule ℤ (Fin 3 → ℤ)) (E : ℕ) (hE : 0 < E)
    (hcontain : ∀ v : Fin 3 → ℤ, E • v ∈ L) :
    ZLattice.covolume (IntegralPlaneLattice.latticeIn x L) =
      (L.toAddSubgroup.index : ℝ) * ‖toEuclidean x‖ /
        (pairingDivisor L.toAddSubgroup x : ℝ) := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp hx
  have hg := (pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz E hE hcontain).1
  obtain ⟨u, hu, hval⟩ := exists_pairing_eq_divisor L.toAddSubgroup x
  have hc := IntegralPlaneLattice.latticeIn_covolume x z hz L (E : ℤ)
    (by exact_mod_cast Nat.ne_of_gt hE)
    (by simpa only [Nat.cast_smul_eq_nsmul] using hcontain)
    (pairingDivisor L.toAddSubgroup x : ℤ) (by exact_mod_cast hg)
    (fun v => pairingDivisor_dvd_pairing L.toAddSubgroup x v v.property)
    ⟨u, hu⟩ hval
  simpa only [Int.cast_natCast, IntegralPlaneLattice.castVec,
    PrimitiveNormal.toEuclidean] using hc

theorem weighted_lattice_shell_le
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hR : B ^ e ≤ 2 * R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (T : ∀ x : Fin 3 → ℤ, Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : ∀ x : Fin 3 → ℤ, (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ W₀)
    (hshort : ∀ x ∈ S, ∀ a ∈ T x, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ x ∈ S, ∀ a ∈ T x, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)])
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  classical
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  have hE : (B ^ e : ℕ) > 0 := pow_pos hB.pos _
  apply ZeroShell.affine_shell_sum_le S
    (fun x => ∑ a ∈ T x, W x a)
    (fun x => (pairingDivisor L.toAddSubgroup x : ℝ))
    (fun x => ‖toEuclidean x‖)
    (fun x => ZLattice.covolume (IntegralPlaneLattice.latticeIn x L))
    (R : ℝ) ((B : ℝ) ^ (b + e))
    (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) 1024
    (by exact_mod_cast hRpos) (by positivity) (by positivity)
  · intro x hx
    obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx)
    exact_mod_cast (pairingDivisor_pos_and_dvd L.toAddSubgroup x z hz
      (B ^ e) hE hcontain).1
  · exact fun x hx => (hnorm x hx).1
  · intro x hx
    rw [canonical_pairing_covolume x (hprimitive x hx) L (B ^ e) hE hcontain,
      hindex, Nat.cast_pow]
  · intro x hx
    obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one x).mp (hprimitive x hx)
    exact weighted_lattice_fibre_le x z hz L (B ^ e) hE hcontain
      (T x) (W x) N W₀ hN hW₀ (hW x hx) (hshort x hx) (hpair x hx)
  · exact pairing_moment_euclidean_shell S L.toAddSubgroup C B R b e k
      hB hR hek P Q hC (fun x hx => (hnorm x hx).2) hprimitive hcontain hrows

theorem weighted_lattice_shell_le_of_short_exclusion
    (S : Finset (Fin 3 → ℤ)) (L : Submodule ℤ (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hRpos : 0 < R)
    (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hnorm : ∀ x ∈ S, (R : ℝ) ≤ ‖toEuclidean x‖ ∧
      ‖toEuclidean x‖ < 2 * (R : ℝ))
    (hprimitive : ∀ x ∈ S, IsPrimitive x)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L)
    (T : ∀ x : Fin 3 → ℤ, Finset (Fin 3 → IntegralPlaneLattice.latticeIn x L))
    (W : ∀ x : Fin 3 → ℤ, (Fin 3 → IntegralPlaneLattice.latticeIn x L) → ℝ)
    (N W₀ : ℝ) (hN : 0 ≤ N) (hW₀ : 0 ≤ W₀)
    (hW : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ W₀)
    (hshort : ∀ x ∈ S, ∀ a ∈ T x, ∀ i,
      ‖(a i : IntegralPlaneLattice.plane x)‖ ≤ 4 * N)
    (hpair : ∀ x ∈ S, ∀ a ∈ T x, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : IntegralPlaneLattice.plane x),
        (a j : IntegralPlaneLattice.plane x)])
    (hexclude : ∀ x ∈ S, ∀ a ∈ T x, 0 < W x a →
      ((B : ℝ) ^ k) ^ 2 < ‖toEuclidean x‖)
    (hindex : L.toAddSubgroup.index = B ^ (b + e)) :
    (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤
      (W₀ * (144 * Real.pi) ^ 3 * N ^ 6) * 1024 /
        ((B : ℝ) ^ (b + e)) ^ 2 := by
  by_cases hR : B ^ e ≤ 2 * R
  · exact weighted_lattice_shell_le S L C B R b e k hB hRpos hR hek
      P Q hC hnorm hprimitive hcontain hrows T W N W₀ hN hW₀
      hW hshort hpair hindex
  · have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB.one_le
    have hpow1 : (1 : ℝ) ≤ (B : ℝ) ^ k := one_le_pow₀ hB1
    have hEH : (B : ℝ) ^ e ≤ (B : ℝ) ^ k := pow_le_pow_right₀ hB1 hek
    have hsmall : (2 : ℝ) * (R : ℝ) < (B : ℝ) ^ e := by
      exact_mod_cast (Nat.lt_of_not_ge hR)
    have hwzero : ∀ x ∈ S, ∀ a ∈ T x, W x a ≤ 0 := by
      intro x hx a ha
      apply le_of_not_gt
      intro hw
      have hs := (hnorm x hx).2
      have hl := hexclude x hx a ha hw
      nlinarith
    calc
      (∑ x ∈ S, ∑ a ∈ T x, W x a) ≤ 0 :=
        Finset.sum_nonpos (fun x hx => Finset.sum_nonpos (hwzero x hx))
      _ ≤ _ := by positivity

end Problem355.ZeroAffineShell

end OAI
