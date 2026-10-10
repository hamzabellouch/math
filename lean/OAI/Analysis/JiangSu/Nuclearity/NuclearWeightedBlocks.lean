import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ComplexScalar

namespace OAI

noncomputable section
open Pureness NuclearTrace
open scoped ComplexOrder

namespace DirectPacking
open CurrentMain DirectComparison

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma global_partition_bound_corner {N : Type} [Fintype N]
    (v : N → D) (x : unitary D) {r : D} (hr : IsStarProjection r)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (q j) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (q j)*star (x : D)))^2 < δ^2)
    (P : ProjectionPartition r) (τ : TracialState D) :
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j) -
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))) ≤ δ := by
  classical
  let q : Option P.Index → D := Option.elim' (1-r) P.piece
  have hq : ∀ j, IsStarProjection (q j) := by
    intro j
    cases j with
    | none => exact hr.one_sub
    | some j => exact P.isProjection j
  have hs : ∑ j, q j = 1 := by
    rw [Fintype.sum_option]
    change (1-r)+(∑ j, P.piece j) = 1
    rw [P.sum_eq]
    abel
  have hb := h (Option P.Index) q hq hs τ
  rw [Fintype.sum_option] at hb
  change (traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))+
    (∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D))))^2 < δ^2 at hb
  have hnon := traceOneNorm_nonneg τ
    (weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)-
    (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (1-r)*star (x : D))
  have hsum : 0 ≤ ∑ j, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)-
      (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) v (P.piece j)*star (x : D)) :=
    Finset.sum_nonneg fun j _ => traceOneNorm_nonneg τ _
  exact (le_add_of_nonneg_left hnon).trans
    ((sq_lt_sq₀ (add_nonneg hnon hsum) hδ).mp hb).le

variable [TraceFamily D]

theorem nuclear_weighted_block_family
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (N : Type) (_ : Fintype N) (v : N → A),
      (∑ i, star (v i)*v i = 1) ∧ (∑ i, v i*star (v i) = 1) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : RestrictedTracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : N => (1 : ℝ))
          (fun i => ι (v i)) r) ≤ η^2) ∧
      (∀ x ∈ K, ∀ τ : RestrictedTracialState D,
        ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*η) := by
  classical
  let K' := K.image (fun x => star x)
  obtain ⟨N,instN,a,ha1,ha2,ha⟩ := nuclear_global_partition_averaging hA ι hT K'
    (show 0 < (η^2)^2 by positivity)
  let v : N → A := fun i => star (a i)
  have hv : ∑ i, star (v i)*v i = 1 := by simpa only [v,star_star] using ha2
  have hv' : ∑ i, v i*star (v i) = 1 := by simpa only [v,star_star] using ha1
  have hvD : ∑ i, star (ι (v i))*ι (v i) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι hv
  refine ⟨N,instN,v,hv,hv',?_⟩
  intro r hr
  let KD := K.image (mapUnitary ι)
  have hc : ∀ r₀ : D, IsStarProjection r₀ → r₀ ≤ r → ∀ P : ProjectionPartition r₀, ∀ x ∈ KD, ∀ τ : RestrictedTracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s)*star (x : D)) ≤ η^2 := by
    intro r₀ hr₀ _ P x hx τ
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply global_partition_bound_corner (fun i => ι (v i)) (mapUnitary ι y) hr₀ (sq_nonneg η) _ P τ
    intro J _ q hq hsum σ
    have he := ha (star y) (Finset.mem_image_of_mem _ hy) J q hq hsum σ
    simpa only [weightedAverage,one_smul,v,map_star,star_star,Unitary.coe_star,mapUnitary_coe] using he
  obtain ⟨F,hcompress,hmass,henergy⟩ := weighted_family_of_kraus_average hsupply
    (fun i => ι (v i)) hvD KD hη hη1 hr hc
  refine ⟨F,?_,hmass,?_⟩
  · intro j x hx
    exact hcompress j (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)
  · intro x hx
    exact henergy (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)

end DirectPacking
end

noncomputable section
open Pureness
open scoped ComplexOrder

namespace DirectPacking
open CurrentMain DirectComparison

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

theorem nuclear_prepared_row_blocks
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A)) (S : Finset (BistochasticTest A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (M σ : ℝ) (L : Finset (unitary A)) (V : BistochasticTest A),
      1 ≤ M ∧ 0 < σ ∧ σ ≤ η ∧ M*σ ≤ η ∧ K ⊆ L ∧
      (∀ W ∈ S, ∀ (J : Type) [Fintype J] (y : J → D) (τ : RestrictedTracialState D)
        (B : ℝ), 0 ≤ B →
        (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
        ∑ j, (W.map ι).energy τ (y j) ≤ M*B) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
        (∀ j, ∀ x ∈ L, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
          ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < σ) ∧
        (∀ τ : RestrictedTracialState D,
          traceOneNorm τ (F.weightedSum-weightedAverage (fun _ => (1 : ℝ)) (V.map ι).coeff r) ≤ η^2) ∧
        (∀ x ∈ L, ∀ τ : RestrictedTracialState D,
          ∑ j, F.weight j*traceTwoNorm τ (ι (x : A)*F.range j-F.range j*ι (x : A))^2 ≤ 6*σ) := by
  classical
  choose L₀ hL₀ using fun W : BistochasticTest A => W.relative_unitary_tests ι
  let L := K ∪ S.biUnion L₀
  let M : ℝ := 1+∑ W ∈ S, 4*(W.size : ℝ)
  have hM : 1 ≤ M := by
    have hs : 0 ≤ ∑ W ∈ S, 4*(W.size : ℝ) := Finset.sum_nonneg fun W _ => by positivity
    exact le_add_of_nonneg_right hs
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let σ := η/M
  have hσ : 0 < σ := div_pos hη hMpos
  have hση : σ ≤ η := (div_le_self hη.le hM)
  have hσ1 : σ < 1 := hση.trans_lt hη1
  obtain ⟨N,instN,v,hv,hv',hblocks⟩ := nuclear_weighted_block_family hA ι hsupply hT L hσ hσ1
  let V := BistochasticTest.ofFamily v hv hv'
  refine ⟨M,σ,L,V,hM,hσ,hση,?_,Finset.subset_union_left,?_,?_⟩
  · dsimp [σ]; rw [mul_div_cancel₀ _ (ne_of_gt hMpos)]
  · intro W hW J _ y τ B hB htest
    have hcoeff : 4*(W.size : ℝ) ≤ M := by
      have hh := Finset.single_le_sum (f := fun W : BistochasticTest A => 4*(W.size : ℝ))
        (fun W _ => by positivity) hW
      dsimp [M]
      linarith
    exact (hL₀ W J y τ B hB (fun u hu => htest u
      (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨W,hW,hu⟩)))).trans
        (mul_le_mul_of_nonneg_right hcoeff hB)
  · intro r hr
    obtain ⟨F,hcomp,hmass,henergy⟩ := hblocks r hr
    refine ⟨F,hcomp,?_,henergy⟩
    intro τ
    rw [show (V.map ι).coeff = ((BistochasticTest.ofFamily v hv hv').map ι).coeff from rfl,
      BistochasticTest.ofFamily_average ι v hv hv' r]
    exact (hmass τ).trans ((sq_le_sq₀ hσ.le hη.le).mpr hση)

end DirectPacking
end

end OAI
