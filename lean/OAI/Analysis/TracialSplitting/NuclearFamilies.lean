import OAI.Analysis.TracialSplitting.BlockAveraging

namespace OAI


section

noncomputable section

open Pureness NuclearTrace

open scoped ComplexOrder

namespace CurrentMain

section NuclearWeightedBlocks

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
  nlinarith

theorem nuclear_weighted_block_family
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hT : Nonempty (TracialState D)) (K : Finset (unitary A))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ (N : Type) (_ : Fintype N) (v : N → A),
      (∑ i, star (v i)*v i = 1) ∧ (∑ i, v i*star (v i) = 1) ∧
      ∀ r : D, IsStarProjection r → ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j*ι (x : A)*F.range j-(F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : TracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : N => (1 : ℝ))
          (fun i => ι (v i)) r) ≤ η^2) ∧
      (∀ x ∈ K, ∀ τ : TracialState D,
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
  have hc : ∀ P : ProjectionPartition r, ∀ x ∈ KD, ∀ τ : TracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s) -
        (x : D)*weightedAverage (fun _ : N => (1 : ℝ)) (fun i => ι (v i)) (P.piece s)*star (x : D)) ≤ η^2 := by
    intro P x hx τ
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    apply global_partition_bound_corner (fun i => ι (v i)) (mapUnitary ι y) hr (sq_nonneg η) _ P τ
    intro J _ q hq hsum σ
    have he := ha (star y) (Finset.mem_image_of_mem _ hy) J q hq hsum σ
    simpa only [weightedAverage,one_smul,v,map_star,star_star,Unitary.coe_star,mapUnitary_coe] using he
  obtain ⟨F,hcompress,hmass,henergy⟩ := weighted_family_of_kraus_average hRR
    (fun i => ι (v i)) hvD KD hη hη1 hr hc
  refine ⟨F,?_,hmass,?_⟩
  · intro j x hx
    exact hcompress j (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)
  · intro x hx
    exact henergy (mapUnitary ι x) (Finset.mem_image_of_mem _ hx)

end NuclearWeightedBlocks

end CurrentMain

end

end

end OAI
