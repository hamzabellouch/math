import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearWeightedBlocks
import OAI.Analysis.JiangSu.Comparison.PrecisePackingRound
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixPackingCornerRound
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixProjectionGenerators

namespace OAI

noncomputable section
open Pureness
open scoped ComplexOrder

namespace DirectPacking
open CurrentMain DirectComparison

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

theorem matrix_packing_from_nuclearity
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    (hT : Nonempty (TracialState D))
    (hcoef : CoefficientSupply (D := D)) (hinsert : InsertionSupply (D := D))
    {m : ℕ} (hm : 0 < m)
    (hmat : ∀ e : D, IsStarProjection e → ∃ p : D, ∃ V : ProjectionRow (Fin m) p,V.sample p=e)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) (n : ℕ)
    (K : Finset (unitary A)) (S : Finset (BistochasticTest A)) :
    ∃ Q : OrthogonalProjectionPair D, ∃ C : MatrixPackingCertificate Q.total m,
      PackingBounds ι Q K η n ∧
      (∀ W ∈ S, ∀ τ : RestrictedTracialState D,
        ∑ i, Q.energy τ (ι (W.coeff i)) ≤ packingEnergy η n) ∧
      (∀ τ : RestrictedTracialState D,C.gap τ≤packingEnergy η n) ∧
      (∀ P : CStarMatrix (Fin m) (Fin m) ℂ, IsStarProjection P →
        Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1 →
        ∀ x∈K, ∀ τ : RestrictedTracialState D,C.energy τ (ι (x:A)) P≤packingEnergy η n) := by
  classical
  induction n generalizing S with
  | zero =>
    refine ⟨.zero,(MatrixPackingCertificate.zero m).rebase (by simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.total]),?_,?_,?_,?_⟩
    · constructor
      · intro x hx τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.energy]
      · intro τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.remaining,
          OrthogonalProjectionPair.total,τ.normalized]
      · intro x hx τ
        simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.balance]
    · intro W hW τ
      simp [OrthogonalProjectionPair.zero,OrthogonalProjectionPair.energy]
    · intro τ
      simp [MatrixPackingCertificate.gap,MatrixPackingCertificate.zero,MatrixPackingCertificate.rebase,packingEnergy]
      exact le_of_eq (Finset.sum_eq_zero (fun i _ => Empty.elim i))
    · intro P _ _ x _ τ
      simp [MatrixPackingCertificate.energy,MatrixPackingCertificate.zero,MatrixPackingCertificate.rebase,packingEnergy]
      exact le_of_eq (Finset.sum_eq_zero (fun i _ => Empty.elim i))
  | succ n ih =>
    obtain ⟨M,σ,L,V,hM,hσ,hση,hMσ,hKL,hL,hblocks⟩ :=
      nuclear_prepared_row_blocks hA ι hsupply hT K S hη hη1
    obtain ⟨Q,C,hQ,hQS,hCgap,hCenergy⟩ := ih (insert V S)
    obtain ⟨F,hcomp,hclose,hblock⟩ := hblocks (1-Q.total) Q.total_projection.one_sub
    let LD := L.image (mapUnitary ι)
    let δ := η^2/(M*((Fintype.card (F.Index × Bool) : ℝ)+1))
    have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcompD : ∀ j, ∀ x ∈ LD, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j*(x : D)*F.range j-(F.row j).matrix (F.base j) H‖ < σ := by
      intro j x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact hcomp j u hu
    obtain ⟨R,hRcorner⟩ := exists_precise_corner_round hcoef hinsert Q.total_projection F LD
      hη hη1 hση hδ hcompD
    have hRprec := fun a => (hRcorner a).1
    obtain ⟨φ,hφ1,hφ⟩ := exists_round_matrix_maps hm hmat R hη hσ.le (hση.trans_lt hη1) hRcorner hcompD
    let C' := (C.append Q.total_projection R φ).rebase (Q.appendRound_total R).symm
    have herror0 : 0 ≤ R.totalError := by
      dsimp [SampledPackingRound.totalError]
      positivity
    have hMerror : M*R.totalError ≤ η^2 := by
      dsimp [SampledPackingRound.totalError,δ]
      have hc : 0 ≤ (Fintype.card (F.Index × Bool) : ℝ) := by positivity
      apply (mul_le_mul_iff_right₀ (show 0 < M*((Fintype.card (F.Index × Bool) : ℝ)+1) by positivity)).mp
      field_simp
      nlinarith [sq_nonneg η]
    have herror : R.totalError ≤ η^2 :=
      (le_mul_of_one_le_left herror0 hM).trans hMerror
    have hE : 0 ≤ packingEnergy η n := packingEnergy_nonneg hη.le n
    have hold (τ : RestrictedTracialState D) :
        (τ.functional (Q.total*weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ≤
          4*packingEnergy η n := by
      apply ((V.map ι).overlap_le τ Q.total_projection).trans
      have ht : (V.map ι).energy τ Q.total ≤ ∑ i, Q.energy τ (ι (V.coeff i)) :=
        Finset.sum_le_sum fun i _ => Q.total_energy_le τ (ι (V.coeff i))
      exact (ht.trans (hQS V (Finset.mem_insert_self _ _) τ)).trans (by linarith)
    have hmass (τ : RestrictedTracialState D) :
        (τ.functional (1-Q.total)).re-η^2 ≤
          (τ.functional (weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ∧
        (τ.functional (weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff (1-Q.total))).re ≤
          (τ.functional (1-Q.total)).re := by
      rw [kraus_average_trace τ _ (V.map ι).col]
      constructor <;> nlinarith [sq_nonneg η]
    have hblockD : ∀ x ∈ LD, ∀ τ : RestrictedTracialState D,
        ∑ j, F.weight j*traceTwoNorm τ ((x : D)*F.range j-F.range j*(x : D))^2 ≤ 6*σ := by
      intro x hx τ
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact hblock u hu τ
    have H : R.Estimates (packingEnergy η n) := R.estimates_of_average Q.total_projection hη hη1 hE
      (weightedAverage_nonneg (fun _ => (1 : ℝ)) (V.map ι).coeff (fun _ => zero_le_one)
        Q.total_projection.one_sub.nonneg)
      ((V.map ι).average_le_one Q.total_projection.one_sub)
      herror hmass hclose (fun x hx τ => (hblockD x hx τ).trans (by linarith)) hold
    refine ⟨Q.appendRound R,C',?_,?_,?_,?_⟩
    · constructor
      · intro x hx τ
        rw [packingEnergy_succ]
        apply (Q.appendRound_energy R τ (ι (x : A))).trans
        exact add_le_add (hQ.energy x hx τ)
          (H.inserted_energy (mapUnitary ι x) (Finset.mem_image_of_mem _ (hKL hx)) τ)
      · intro τ
        change (τ.functional (1-(Q.appendRound R).total)).re ≤ _
        rw [Q.appendRound_total R]
        apply (H.remaining τ).trans
        apply le_trans _ (packingRemainder_step hη.le n)
        apply add_le_add
        · exact add_le_add (mul_le_mul_of_nonneg_left (hQ.remaining τ) (sub_nonneg.mpr hη1.le)) le_rfl
        · exact mul_le_mul_of_nonneg_left (H.overlap_incr τ) (by norm_num)
      · intro x hx τ
        apply (Q.appendRound_balance R τ (ι (x : A))).trans
        apply le_trans _ (packingBalance_step hη.le n)
        exact add_le_add (hQ.balance x hx τ)
          (H.balance R hη herror τ (mapUnitary ι x) (Finset.mem_image_of_mem _ (hKL hx)))
    · intro W hW τ
      have hu : ∀ u ∈ L,
          ∑ a, traceTwoNorm τ (ι (u : A)*R.sampled a-R.sampled a*ι (u : A))^2 ≤
            36*σ*η+10*R.totalError := by
        intro u hu
        have hb := R.precise_sampled_energy_sum hRprec τ (mapUnitary ι u)
          (Finset.mem_image_of_mem _ hu)
        have hb' := mul_le_mul_of_nonneg_left (hblock u hu τ) hη.le
        have hc := add_le_add (H.sampled_upper τ) (H.target_upper τ)
        have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 6*σ)
        change (∑ a, traceTwoNorm τ (ι (u : A)*R.sampled a-R.sampled a*ι (u : A))^2) ≤
          η*(∑ j, F.weight j*traceTwoNorm τ (ι (u : A)*F.range j-F.range j*ι (u : A))^2)+
            6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError at hb
        nlinarith
      have hs := hL W hW (F.Index × Bool) R.sampled τ
        (36*σ*η+10*R.totalError) (by positivity) hu
      have hs' : ∑ a, (W.map ι).energy τ (R.sampled a) ≤ 46*η^2 := by
        have hmσ := mul_le_mul_of_nonneg_right hMσ hη.le
        nlinarith
      have hi := R.inserted_row_energy (W.map ι) τ
      have hb := H.overlap_upper τ
      have hinc : ∑ a, (W.map ι).energy τ (R.inserted a) ≤
          1000*η*(packingEnergy η n+η) := by
        nlinarith [mul_nonneg hη.le hE,sq_nonneg η]
      have hp := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
        Q.appendRound_energy R τ (ι (W.coeff i))
      rw [Finset.sum_add_distrib,Finset.sum_comm] at hp
      change (∑ i, (Q.appendRound R).energy τ (ι (W.coeff i))) ≤
        (∑ i, Q.energy τ (ι (W.coeff i)))+(∑ a, (W.map ι).energy τ (R.inserted a)) at hp
      rw [packingEnergy_succ]
      exact hp.trans (add_le_add (hQS W (Finset.mem_insert_of_mem hW) τ) hinc)

    · intro τ
      change (C.append Q.total_projection R φ).gap τ≤packingEnergy η (n+1)
      rw [C.append_gap,packingEnergy_succ]
      simp_rw [hφ1]
      have hd := Finset.sum_le_sum fun a (_ : a∈Finset.univ) => (R.bounds a).inserted_distance τ
      have ho := H.overlap_upper τ
      have hh : (∑ a,traceTwoNorm τ (R.inserted a-R.sampled a)^2)≤5*R.overlap τ := by
        simpa only [←Finset.mul_sum,SampledPackingRound.overlap] using hd
      have hc := hCgap τ
      nlinarith [mul_nonneg hη.le hE,sq_nonneg η]
    · intro P hP htr x hx τ
      change (C.append Q.total_projection R φ).energy τ (ι (x:A)) P≤packingEnergy η (n+1)
      rw [C.append_energy,packingEnergy_succ]
      have hb := hφ P hP htr (mapUnitary ι x) (Finset.mem_image_of_mem _ (hKL hx)) τ
      have hb' := mul_le_mul_of_nonneg_left (hblock x (hKL hx) τ) hη.le
      have hc := add_le_add (H.sampled_upper τ) (H.target_upper τ)
      have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0≤6*σ)
      have hmσ := mul_le_mul_of_nonneg_right hση hη.le
      have he := hCenergy P hP htr x hx τ
      change (∑ a,traceTwoNorm τ (ι (x:A)*φ a P-φ a P*ι (x:A))^2)≤
        η*(∑ j,F.weight j*traceTwoNorm τ (ι (x:A)*F.range j-F.range j*ι (x:A))^2)+
        6*σ*(R.sampledMass τ+R.targetMass τ)+10*R.totalError at hb
      nlinarith [mul_nonneg hη.le hE,sq_nonneg η]

end DirectPacking

end

end OAI
