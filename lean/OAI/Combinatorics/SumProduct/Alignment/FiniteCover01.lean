import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FourierObstruction01
import OAI.Combinatorics.SumProduct.Alignment.ProgressionPartition01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
end
 

 
section
noncomputable section
open scoped BigOperators
namespace FactorProgression
open CubeFaces CubePolynomials RationalLattice ProgressionPartition
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (Γ : Subgroup G) {m : ℕ} (c : RealCoordinates (H.level 2) m)
variable [mtr : MetricSpace (G⧸Γ)]
local instance metricQuotientTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace
variable [hcpt : CompactSpace (G⧸Γ)] [hcsm : ContinuousSMul G (G⧸Γ)]

lemma cell_smooth_bound (B : ℝ) (hB : 0 ≤ B) {J K T N a n r : ℕ}
    (hJ : 0<J) (hN : 0<N) (hn : n<K) (hM : J*K*T ≤ N) :
    (B/N)*|(((a*K+n)*T+r:ℕ):ℝ)-((a*K*T+r:ℕ):ℝ)| ≤ B/J := by
  have hj : (0:ℝ)<J := by exact_mod_cast hJ
  have hnn : (0:ℝ)<N := by exact_mod_cast hN
  have he : (((a*K+n)*T+r:ℕ):ℝ)-((a*K*T+r:ℕ):ℝ)=(n:ℝ)*T := by push_cast; ring
  rw [he,abs_of_nonneg (by positivity)]
  have hlen : ((n:ℝ)*T)*J ≤ N := by
    exact_mod_cast (show n*T*J ≤ N from (by
      calc
        _ = J*n*T := by ring
        _ ≤ J*K*T := Nat.mul_le_mul_right T (Nat.mul_le_mul_left J hn.le)
        _ ≤ N := hM))
  have hq : ((n:ℝ)*T)/N ≤ 1/(J:ℝ) := (div_le_div_iff₀ hnn hj).mpr (by simpa using hlen)
  calc
    _ = B*(((n:ℝ)*T)/N) := by ring
    _ ≤ B*(1/(J:ℝ)) := mul_le_mul_of_nonneg_left hq hB
    _ = _ := by ring

include hcpt hcsm in
 

theorem factor_progression_obstruction (B δ : ℝ) (hB : 0<B) (hδ : 0<δ)
    (Tmax : ℕ) (hTmax : 0<Tmax) :
    ∃ J : ℕ, 0<J ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ, 0<T → T ≤ Tmax →
      ∀ (C : Set G), (∀ g : G, ∃ v∈C, (QuotientGroup.mk g : G⧸Γ)=QuotientGroup.mk v) →
      ∀ (L : Filtration G), L.level 0=⊤ →
      ∀ (f f' : ℤ → G) (e b : ℤ → H.level 2),
      f'∈polynomials L 0 → (∀ z, f z=(e z).val*f' z*(b z).val) →
      Function.Periodic (fun z => (QuotientGroup.mk (b z).val : G⧸Γ)) (T:ℤ) →
      (∀ z : ℤ, |(z:ℝ)| ≤ N → ‖c.coord (e z)‖ ≤ B) →
      (∀ z w : ℤ, |(z:ℝ)| ≤ N → |(w:ℝ)| ≤ N →
        ‖c.coord (e z*(e w)⁻¹)‖ ≤ (B/N)*|(z:ℝ)-(w:ℝ)|) →
      ∀ F : C(G⧸Γ,ℂ), LipschitzWith 1 F → ‖F‖ ≤ 1 →
      ∀ μ : ℂ, ‖μ‖ ≤ 1 → δ*N ≤ ‖∑ i∈Finset.range N, (F (QuotientGroup.mk (f i))-μ)‖ →
      let K : ℕ := N/(J*T)
      0<K ∧ J*K*T ≤ N ∧ N ≤ 2*J*Tmax*K ∧
      ∃ a<J, ∃ r<T, ∃ v∈C,
        ‖c.coord (e ((a*K*T+r:ℕ):ℤ))‖ ≤ B ∧
        (fun z : ℤ => v⁻¹*f' ((T:ℤ)*z+(a*K*T+r:ℕ))*v)∈polynomials L 0 ∧
        δ/4*K ≤ ‖∑ n∈Finset.range K,
          (F (((e ((a*K*T+r:ℕ):ℤ)).val*v) •
            (QuotientGroup.mk (v⁻¹*f' (((a*K+n)*T+r:ℕ):ℤ)*v) : G⧸Γ))-μ)‖ := by
  let : ContinuousSMul (H.level 2) (G⧸Γ) := ⟨by
    change Continuous (fun p : H.level 2 × (G⧸Γ) => (p.1.val:G) • p.2)
    fun_prop⟩
  obtain ⟨u,hu,hsmall⟩ := CompactActionFreeze.small_displacement (X:=G⧸Γ) c.coord (funext c.one_coord) (δ/4) (by positivity)
  obtain ⟨J,hJreal⟩ := exists_nat_gt (B/u)
  have hJ : 0<J := by
    have hh : (0:ℝ)<J := lt_trans (div_pos hB hu) hJreal
    exact_mod_cast hh
  have hBJ : B/(J:ℝ) ≤ u := by
    apply (div_le_iff₀ (by exact_mod_cast hJ)).mpr
    have hh := (div_lt_iff₀ hu).mp hJreal
    nlinarith
  obtain ⟨N₀,hN₀,hscale⟩ := uniform_scales J Tmax hJ hTmax δ hδ
  refine ⟨J,hJ,N₀,hN₀,?_⟩
  intro N hN T hT hTT C hC L hL f f' e b hfp hfac hper hev hed F hFL hF μ hμ hlarge
  let K : ℕ := N/(J*T)
  obtain ⟨hK,hM,hcomp,htail⟩ := hscale N hN T hT hTT
  change 0<K at hK
  change J*K*T ≤ N at hM
  change N ≤ 2*J*Tmax*K at hcomp
  change 2*((N-J*K*T:ℕ):ℝ) ≤ δ*N/4 at htail
  have hn : 0<N := hN₀.trans_le hN
  choose v hv hvq using (fun r : ℕ => hC (b (r:ℤ)).val)
  let g : ℕ → ℕ → ℕ → ℂ := fun a r n =>
    F (((e ((a*K*T+r:ℕ):ℤ)).val*v r) • (QuotientGroup.mk ((v r)⁻¹*f' (((a*K+n)*T+r:ℕ):ℤ)*v r) : G⧸Γ))
  have harg {a n r : ℕ} (ha : a<J) (hkn : n<K) (hr : r<T) :
      |((((a*K+n)*T+r:ℕ):ℤ):ℝ)| ≤ N := by
    have hh := (cell_lt ha hkn hr).le.trans hM
    rw [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hh
  have hfreeze (a : ℕ) (ha : a<J) (r : ℕ) (hr : r<T) (n : ℕ) (hkn : n<K) :
      ‖F (QuotientGroup.mk (f (((a*K+n)*T+r:ℕ):ℤ)))-g a r n‖ ≤ δ/4 := by
    let x : G⧸Γ := ((e ((a*K*T+r:ℕ):ℤ)).val*v r) • QuotientGroup.mk ((v r)⁻¹*f' (((a*K+n)*T+r:ℕ):ℤ)*v r)
    let d : H.level 2 := e (((a*K+n)*T+r:ℕ):ℤ)*(e ((a*K*T+r:ℕ):ℤ))⁻¹
    have hs : ‖c.coord d‖ ≤ u := by
      refine (hed _ _ (harg ha hkn hr) ?_).trans ((cell_smooth_bound B hB.le hJ hn hkn hM).trans hBJ)
      simpa using harg ha hK hr
    have hex : (QuotientGroup.mk (f (((a*K+n)*T+r:ℕ):ℤ)) : G⧸Γ)=d • x := by
      have hh := periodic_factor_coset Γ f (fun z => (e z).val) f' (fun z => (b z).val)
        hfac (T:ℤ) hper (r:ℤ) (v r) (hvq r) ((a*K+n):ℕ)
      have heq : (T:ℤ)*((a*K+n:ℕ):ℤ)+(r:ℤ)=(((a*K+n)*T+r:ℕ):ℤ) := by push_cast; ring
      rw [heq] at hh
      change (QuotientGroup.mk (f (((a*K+n)*T+r:ℕ):ℤ)) : G⧸Γ)=(d.val:G) • x
      rw [hh]
      dsimp only [d,x,Subgroup.coe_mul,Subgroup.coe_inv]
      rw [smul_smul]
      congr 1
      group
    calc
      _ = dist (F (QuotientGroup.mk (f (((a*K+n)*T+r:ℕ):ℤ)))) (F x) := by rw [dist_eq_norm]
      _ ≤ dist (QuotientGroup.mk (f (((a*K+n)*T+r:ℕ):ℤ))) x := by simpa using hFL.dist_le_mul _ _
      _ = dist (d • x) x := by rw [hex]
      _ ≤ δ/4 := hsmall d hs x
  obtain ⟨a,ha,r,hr,hobs⟩ := ProgressionPartition.obstruction
    (fun i => F (QuotientGroup.mk (f i))) g μ J K T N δ hδ hn hM
    (fun i => (F.norm_coe_le_norm _).trans hF) hμ htail hfreeze hlarge
  refine ⟨hK,hM,hcomp,a,ha,r,hr,v r,hv r,?_,?_,hobs⟩
  · change ‖c.coord (e ((a*K*T+r:ℕ):ℤ))‖ ≤ B
    apply hev
    simpa only [Nat.add_zero] using harg (n:=0) ha hK hr
  · exact affine_conjugate_polynomial L hL hfp (T:ℤ) (a*K*T+r) (v r)

end FactorProgression
end
end
 

 
section
noncomputable section
open scoped Topology BigOperators
namespace FiniteCoverObservable
open MeasureTheory
variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
  [MulAction G X] [ContinuousSMul G X]

 

def translated (q : C(Y,X)) (g : G) (F : C(X,ℂ)) : C(Y,ℂ) :=
  ⟨fun y => F (g • q y), by fun_prop⟩

omit [IsTopologicalGroup G] [CompactSpace Y] in
lemma continuous_translated (q : C(Y,X)) :
    Continuous (fun p : G × C(X,ℂ) => translated q p.1 p.2) := by
  let A : C((G × C(X,ℂ)) × Y,ℂ) :=
    ⟨fun p => p.1.2 (p.1.1 • q p.2),by fun_prop⟩
  exact A.curry.continuous

 

omit [IsTopologicalGroup G] [CompactSpace Y] in
theorem compact_translated_family (q : C(Y,X)) (C : Set G) (hC : IsCompact C) :
    ∃ K : Set C(Y,ℂ), IsCompact K ∧ ∀ g∈C, ∀ F : C(X,ℂ),
      LipschitzWith 1 F → ‖F‖ ≤ 1 → translated q g F ∈ K := by
  obtain ⟨K,hK,hunit⟩ := FourierObstruction.compact_superset_unit_lipschitz X
  refine ⟨(fun p : G × C(X,ℂ) => translated q p.1 p.2) '' (C ×ˢ K),
    (hC.prod hK).image (continuous_translated q),?_⟩
  intro g hg F hF hFn
  exact ⟨(g,F),⟨hg,hunit F hF hFn⟩,rfl⟩

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

omit [IsTopologicalGroup G] [CompactSpace Y] in
lemma integral_translated (q : C(Y,X)) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [SMulInvariantMeasure G X μ]
    (hmap : Measure.map q ν = μ) (g : G) (F : C(X,ℂ)) :
    (∫ y, translated q g F y ∂ν) = ∫ x, F x ∂μ := by
  change (∫ y, F (g • q y) ∂ν) = _
  rw [← integral_map q.continuous.aemeasurable (by fun_prop : AEStronglyMeasurable (fun x : X => F (g • x)) (Measure.map q ν)),hmap]
  exact integral_smul_eq_self F

 

omit [IsTopologicalGroup G] in
theorem finite_cover_tests (q : C(Y,X)) (C : Set G) (hC : IsCompact C)
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [SMulInvariantMeasure G X μ] (hmap : Measure.map q ν=μ)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ S : Finset {F : C(Y,ℂ) // F ∈ CompactFamilyDescent.lipschitzMaps},
      ∃ η : ℝ, 0<η ∧ ∀ N : ℕ, 0<N → ∀ y : ℕ → Y, ∀ g∈C,
      ∀ F : C(X,ℂ), LipschitzWith 1 F → ‖F‖ ≤ 1 →
        δ ≤ ‖(𝔼 n∈Finset.range N, F (g • q (y n)))-(∫ x, F x ∂μ)‖ →
        ∃ φ∈S, η ≤ ‖FourierObstruction.discrepancy ν N y φ.val‖ := by
  obtain ⟨K,hK,hunit⟩ := compact_translated_family q C hC
  obtain ⟨S,η,hη,htest⟩ := CompactFamilyDescent.finite_lipschitz_obstruction K hK δ 2 hδ (by norm_num)
  refine ⟨S,η,hη,?_⟩
  intro N hN y g hg F hFL hFn hdisc
  apply htest (FourierObstruction.discrepancy ν N y)
    (FourierObstruction.discrepancy_bound ν N hN y)
  refine ⟨translated q g F,hunit g hg F hFL hFn,?_⟩
  change δ ≤ ‖(𝔼 n∈Finset.range N, translated q g F (y n)) - _‖
  rw [integral_translated q μ ν hmap]
  exact hdisc

end FiniteCoverObservable
end
end
 

 
section
noncomputable section
namespace CompactFamilyDescent
open scoped BigOperators
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]

 

theorem finite_unit_lipschitz_obstruction (K : Set C(Y,ℂ)) (hK : IsCompact K)
    (δ B : ℝ) (hδ : 0<δ) (hB : 0<B) :
    ∃ S : Finset C(Y,ℂ), (∀ F∈S, LipschitzWith 1 F ∧ ‖F‖ ≤ 1) ∧
      ∃ η : ℝ, 0<η ∧ ∀ L : C(Y,ℂ) →ₗ[ℂ] ℂ,
        (∀ F, ‖L F‖ ≤ B*‖F‖) → (∃ F∈K, δ ≤ ‖L F‖) →
        ∃ F∈S, η ≤ ‖L F‖ := by
  classical
  obtain ⟨S,η,hη,ht⟩ := finite_lipschitz_obstruction K hK δ B hδ hB
  let C (φ : {F : C(Y,ℂ) // F∈lipschitzMaps}) : NNReal := φ.property.choose
  have hC (φ : {F : C(Y,ℂ) // F∈lipschitzMaps}) : LipschitzWith (C φ) φ.val := φ.property.choose_spec
  let D : NNReal := 1+∑ φ∈S, (‖φ.val‖₊+C φ)
  have hD : 0<D := by dsimp [D]; positivity
  have hDreal : (0:ℝ)<D := hD
  have hc (φ) (hφ : φ∈S) : C φ ≤ D ∧ ‖φ.val‖₊ ≤ D := by
    have hh := Finset.single_le_sum (f:=fun φ => ‖φ.val‖₊+C φ) (fun φ (_ : φ∈S) => by positivity) hφ
    constructor
    · exact (le_add_of_nonneg_left (by positivity)).trans (hh.trans (le_add_of_nonneg_left (by positivity)))
    · exact (le_add_of_nonneg_right (by positivity)).trans (hh.trans (le_add_of_nonneg_left (by positivity)))
  let normalize (φ : {F : C(Y,ℂ) // F∈lipschitzMaps}) : C(Y,ℂ) := ((D:ℂ)⁻¹) • φ.val
  have hn (φ) (hφ : φ∈S) : LipschitzWith 1 (normalize φ) ∧ ‖normalize φ‖ ≤ 1 := by
    have hnorm : ‖(D:ℂ)⁻¹‖ = (D:ℝ)⁻¹ := by simp
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist ((D:ℂ)⁻¹ * φ.val x) ((D:ℂ)⁻¹ * φ.val y) ≤ _
      simp only [dist_eq_norm,← mul_sub,norm_mul,hnorm]
      rw [← dist_eq_norm]
      have hh := (hC φ).dist_le_mul x y
      calc
        _ ≤ (D:ℝ)⁻¹*((C φ:ℝ)*dist x y) := mul_le_mul_of_nonneg_left hh (by positivity)
        _ ≤ (D:ℝ)⁻¹*((D:ℝ)*dist x y) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (show (C φ:ℝ) ≤ D from (hc φ hφ).1) dist_nonneg) (by positivity)
        _ = (1:NNReal)*dist x y := by norm_num; field_simp
    · change ‖(D:ℂ)⁻¹ • φ.val‖ ≤ _
      rw [norm_smul,hnorm]
      have hh : ‖φ.val‖ ≤ (D:ℝ) := (hc φ hφ).2
      calc
        _ ≤ (D:ℝ)⁻¹*(D:ℝ) := mul_le_mul_of_nonneg_left hh (by positivity)
        _ = 1 := inv_mul_cancel₀ hDreal.ne'
  refine ⟨S.image normalize,?_,η/D,div_pos hη hDreal,?_⟩
  · intro F hF
    obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hF
    exact hn φ hφ
  · intro L hL hlarge
    obtain ⟨φ,hφ,hdisc⟩ := ht L hL hlarge
    refine ⟨normalize φ,Finset.mem_image.mpr ⟨φ,hφ,rfl⟩,?_⟩
    change η/(D:ℝ) ≤ ‖L ((D:ℂ)⁻¹ • φ.val)‖
    rw [map_smul,norm_smul]
    have hnorm : ‖(D:ℂ)⁻¹‖=(D:ℝ)⁻¹ := by simp
    rw [hnorm,div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hdisc (by positivity)

end CompactFamilyDescent

end
end
end
end
end

end OAI
