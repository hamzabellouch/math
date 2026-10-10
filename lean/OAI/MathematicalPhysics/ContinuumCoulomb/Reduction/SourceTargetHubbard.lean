import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGraphIndex
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceFiniteBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFrequency

namespace OAI

/-! The literal positive source graph satisfies the finite Hubbard
approximation with uniform exponents fixed before its coordinates are chosen. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceMetadataProgram ContactMediator HubbardGlobal

private theorem source_size_cast (d : BinaryHeisenberg) :
    (SourceContactProgram.size d:ℝ)=(binaryHeisenbergCodec.encode d).length+2 := by
  unfold SourceContactProgram.size SourceMetadataProgram.size
  push_cast
  ring

theorem source_graph_site_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    ((output s d).vertices:ℝ) ≤ (SourceContactProgram.size d:ℝ)^6 := by
  rw [PrefactorSourceContactProgram.electron_count s d hd,source_size_cast]
  exact geometricSource_count s d hd

theorem source_graph_edge_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (graphEdgeCount s d hd:ℝ) ≤ (SourceContactProgram.size d:ℝ)^7 := by
  have hN : (2:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hnat : graphEdgeCount s d hd ≤ 2*(output s d).vertices := by
    rw [PrefactorSourceContactProgram.electron_count s d hd,globalSite_card]
    unfold graphEdgeCount
    omega
  have hr : (graphEdgeCount s d hd:ℝ) ≤ 2*((output s d).vertices:ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ 2*(SourceContactProgram.size d:ℝ)^6 :=
      hr.trans (mul_le_mul_of_nonneg_left (source_graph_site_count s d hd) (by norm_num))
    _ ≤ (SourceContactProgram.size d:ℝ)^7 := by
      calc
        _ ≤ (SourceContactProgram.size d:ℝ)*(SourceContactProgram.size d:ℝ)^6 :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem exists_source_hopping_exponent (freq : ℝ) (A : ℕ) :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
      (m : ℕ) (hm : (output s d).vertices=m+1) (B : ℕ),
      let F := indexedGraph s d hd hm
      let N : ℝ := SourceContactProgram.size d
      (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) →
      ∀ u : Fin (m+1) → PlanarPosition,
      (∑ e, |-coulombHoppingTarget freq (N^(30*B))⁻¹ (F.weight e)
        ‖u (F.left e)-u (F.right e)‖|) ≤ N^v := by
  obtain ⟨v,hv,hbound⟩ := exists_target_hopping_exponent freq 7 (30*A)
  refine ⟨v,hv,fun s d hd m hm B => ?_⟩
  dsimp only
  intro hweights u
  let N : ℝ := SourceContactProgram.size d
  let F := indexedGraph s d hd hm
  have hN : (2:ℝ) ≤ N := by
    change (2:ℝ) ≤ (SourceContactProgram.size d:ℝ)
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hK (e : Fin (graphEdgeCount s d hd)) : 0 ≤ (F.weight e:ℝ) :=
    (inv_nonneg.mpr (pow_nonneg hN0.le _)).trans (hweights e).1
  have hcard : (Fintype.card (Fin (graphEdgeCount s d hd)):ℝ) ≤ N^7 := by
    simpa only [Fintype.card_fin] using source_graph_edge_count s d hd
  have hs := hbound N (N^(30*B))⁻¹ hN
    (inv_nonneg.mpr (pow_nonneg hN0.le _))
    (inv_le_one_of_one_le₀ (one_le_pow₀ hN1))
    (Edge := Fin (graphEdgeCount s d hd)) hcard
    (fun e => ‖u (F.left e)-u (F.right e)‖) (fun e => (F.weight e:ℝ)) hK
    (fun e => (hweights e).2)
  apply le_trans _ hs
  apply Finset.sum_le_sum
  intro e _
  exact (abs_neg _).le

theorem exists_source_target_parameters (rho : ℕ) (hrho : 0 < rho) (s g : ℕ) :
    ∃ A B v q : ℕ, 0 < A ∧ 0 < B ∧ 1 ≤ v ∧ 1 ≤ q ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
      ∀ (m k : ℕ) (hm : (output s d).vertices=m+1), q ≤ k →
      ∀ (D : ℝ) (u : Fin (m+1) → PlanarPosition),
      25*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ D →
      (∀ i j, i ≠ j → D ≤ ‖u i-u j‖) →
      let F := indexedGraph s d hd hm
      let N : ℝ := SourceContactProgram.size d
      let τ := (N^(30*B))⁻¹
      let freq := GaussianFrequency.frequency rho
      let t := fun e => -coulombHoppingTarget freq τ (F.weight e) ‖u (F.left e)-u (F.right e)‖
      (∀ e, (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A)) ∧
      (∑ e, |t e|) ≤ N^v ∧
      |hubbardFermionBottom m (localizedCoulombProfile freq 0) (localizedOffsiteCoulomb freq u)
          F.left F.right t-
        graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e:ℝ))| ≤ (N^g)⁻¹*τ^2 := by
  have hf := manufactured_frequency_positive hrho
  obtain ⟨A,hA,hweights⟩ := PrefactorSourceContactProgram.source_weight_range s
  obtain ⟨E,B,_hE,hB,hfinite⟩ := exists_uniform_target_hubbard_parameters hf 7 A g
  obtain ⟨v,hv,hvbound⟩ := exists_source_hopping_exponent (GaussianFrequency.frequency rho) A
  obtain ⟨q,hq,hqbound⟩ := exists_source_leakage_threshold hf 6
  refine ⟨A,B,v,q,hA,hB,hv,hq,?_⟩
  intro d hd hp m k hm hk D u hD hsep
  dsimp only
  let F := indexedGraph s d hd hm
  let N : ℝ := SourceContactProgram.size d
  let M : ℝ := CalibrationMesh.base (SourceContactProgram.size d)
  have hN : 2 ≤ N := by
    change (2:ℝ) ≤ (SourceContactProgram.size d:ℝ)
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hM : 2 ≤ M := by
    change (2:ℝ) ≤ (CalibrationMesh.base (SourceContactProgram.size d):ℝ)
    exact_mod_cast CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hN
  have hN1 : 1 ≤ N := le_trans (by norm_num : (1:ℝ) ≤ 2) hN
  have hNM : N ≤ M := by
    dsimp [M,CalibrationMesh.base,N]
    rw [Nat.cast_pow]
    exact le_self_pow₀ hN1 (by decide)
  have hMpow (a : ℕ) : M^a=N^(30*a) := by
    dsimp only [M,CalibrationMesh.base,N]
    rw [Nat.cast_pow,← pow_mul]
  have hFweight : F.weight=SourceContactProgram.weights s d hd := indexedGraph_weight s d hd hm
  have hKr (e : Fin (graphEdgeCount s d hd)) : (M^A)⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ M^A := by
    rw [hFweight]
    exact hweights d hd hp e
  have hK (e : Fin (graphEdgeCount s d hd)) : 0 ≤ (F.weight e:ℝ) :=
    (inv_nonneg.mpr (pow_nonneg (le_trans (by norm_num : (0:ℝ) ≤ 2) hM) A)).trans (hKr e).1
  have hcount : (m+1:ℕ) ≤ N^6 := by
    rw [← hm]
    exact source_graph_site_count s d hd
  obtain ⟨hfive,hleak⟩ := hqbound k hk N D hN hD (m+1) hcount
  have heN : (graphEdgeCount s d hd:ℝ) ≤ N^7 := source_graph_edge_count s d hd
  have heM : (graphEdgeCount s d hd:ℝ) ≤ M^7 :=
    heN.trans (pow_le_pow_left₀ hN0.le hNM 7)
  have hloop := indexedGraph_noLoops s d hd hm
  have hsimple := (indexedGraph_simple s d hd hm).hypothesis
  have herr := hfinite M hM _ heM D hfive m u hsep hleak F.left F.right
    (fun e => (F.weight e:ℝ)) hK (fun e => (hKr e).2) hloop hsimple
  have hKpower (e : Fin (graphEdgeCount s d hd)) :
      (N^(30*A))⁻¹ ≤ (F.weight e:ℝ) ∧ (F.weight e:ℝ) ≤ N^(30*A) := by
    simpa only [hMpow] using hKr e
  refine ⟨hKpower,hvbound s d hd m hm B hKpower u,?_⟩
  rw [hMpow B] at herr
  exact herr.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ (pow_pos hN0 g) (pow_le_pow_left₀ hN0.le hNM g)) (sq_nonneg _))

end ContinuumCoulomb

end

end OAI
