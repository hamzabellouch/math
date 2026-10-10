import OAI.Combinatorics.MatchingPSD.MatrixInterpolation

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SampleIndex (d : ℕ) := Fin 5 ⊕ GridIndex d
noncomputable def samplePoint (d : ℕ) (L : ℝ) : SampleIndex d → Point :=
  Sum.elim specialPoint (scaledNode L)

lemma specialPoint_explicit (j : Fin 5) :
    specialPoint j = (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Point) := by
  fin_cases j <;> ext a <;> fin_cases a <;> norm_num [specialPoint, origin, dirP, dirStar, dirA, dirB]

lemma sample_witness {s l d : ℕ} (hs : 1 ≤ s) (hsl : 2*l*d ≤ s) (t : SampleIndex d) :
    ∃ M : Pairing (TripleVertices s), crossVector threeColor M = samplePoint d (2*l) t := by
  rcases t with j | g
  · rw [samplePoint, Sum.elim_inl, specialPoint_explicit]
    exact triple_pairing_five hs j
  · exact triple_pairing_grid hsl g

lemma good_cell_polynomials (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 2*l*d ≤ s →
      ∀ (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ M, (B M).PosSemidef) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      ∀ η : ℝ, 0 ≤ η →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤ η^2 →
      ∃ a : Equiv.Perm (GlobalVertices s q),
      ∃ P : Fin q → Fin r → Fin r → Point → ℝ,
        (∀ i u v, P i u v ∈ lowDegree coord d) ∧
        ∀ i u v t, |cellMatrix i (fun M => B (Pairing.relabel a M))
          (samplePoint d (2*l) t) u v-P i u v (samplePoint d (2*l) t)| ≤ η := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_cross_approximation K
  refine ⟨d,H,hd,?_⟩
  intro s q l r hH hs hsl B hB htr η hη hnum
  let J := Fin q × (Fin r × Fin r)
  let T := SampleIndex d
  let M : T → Pairing (TripleVertices s) := fun t => (sample_witness hs hsl t).choose
  have hM (t : T) : crossVector threeColor (M t) = samplePoint d (2*l) t :=
    (sample_witness hs hsl t).choose_spec
  let g (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) : ℝ :=
    extensionAverage j.1 (fun Z => B (Pairing.relabel a Z) j.2.1 j.2.2) N
  have hg (j : J) (a : Equiv.Perm (GlobalVertices s q)) (p : Equiv.Perm (TripleVertices s)) :
      g j (a * liftLocal j.1 p) = fun N => g j a (Pairing.relabel p N) := by
    funext N
    dsimp only [g]
    rw [extensionAverage_relabel]
    simp only [Pairing.relabel_mul]
  have hgb (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) :
      (g j a N)^2 ≤ (r:ℝ)^2 :=
    extensionAverage_sq_bound j.1 _ (fun Z => hB _) (Nat.cast_nonneg r)
      (fun Z => htr _) j.2.1 j.2.2 N
  obtain ⟨a,P,hP,hbound⟩ := hmain (3*s+1) hH (TripleVertices s)
    (Equiv.Perm (GlobalVertices s q)) J T (tripleEquiv s) (fun _ => threeColor)
      (fun _ c => triple_histogram_pos (by omega) c) (fun _ => M)
      (fun j => liftLocal j.1) g hg (r:ℝ) hgb
  refine ⟨a,fun i u v => P (i,u,v),fun i u v => hP (i,u,v),?_⟩
  intro i u v t
  let E (j : J) (t : T) :=
    predicateAverage (fun N => crossVector threeColor N = crossVector threeColor (M t)) (g j a) -
      P j (crossVector threeColor (M t))
  have hjt : (E (i,u,v) t)^2 ≤ ∑ j, ∑ t, (E j t)^2 := by
    exact (Finset.single_le_sum (fun z _ => sq_nonneg (E (i,u,v) z)) (Finset.mem_univ t)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun z _ => sq_nonneg (E j z)))
        (Finset.mem_univ (i,u,v)))
  have hb : (∑ j, ∑ t, (E j t)^2) ≤ η^2 := by
    apply hbound.trans
    have heq : (Fintype.card J : ℝ)*(Fintype.card T)*((2*(3*s+1:ℕ):ℝ)^(2*K))⁻¹*(r:ℝ)^2 =
        (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ := by
      simp only [J, T, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [heq]
    exact hnum
  have hab : |E (i,u,v) t| ≤ η := (sq_le_sq₀ (abs_nonneg _) hη).mp
    (by simpa only [sq_abs] using hjt.trans hb)
  have he : E (i,u,v) t = cellMatrix i (fun Z => B (Pairing.relabel a Z))
      (samplePoint d (2*l) t) u v-P (i,u,v) (samplePoint d (2*l) t) := by
    rw [cellMatrix_apply]
    dsimp only [E, cellAverage, g]
    rw [hM]
  rwa [he] at hab

end MatchingInterpolation

end OAI
