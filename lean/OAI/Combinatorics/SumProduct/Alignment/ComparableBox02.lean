import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CorrectedBox06
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace ComparableBoxLeibman
open MeasureTheory
variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma rectMean_smul (n : ℕ) (L : Fin n→ℕ) (z : ℂ) (f : (Fin n→ℕ)→ℂ) :
    rectMean n L (fun x => z*f x)=z*rectMean n L f := by
  simp only [rectMean_eq_fin, ← Finset.mul_expect]

omit [BorelSpace Y] in
lemma normalized_rect_observable [BorelSpace Y] (μ : Measure Y) (v : ℕ) (L : Fin v→ℕ)
    (p : (Fin v→ℕ)→Y) (B : NNReal) (hB : 0<B) (η : ℝ)
    (F : C(Y,ℂ)) (hFL : LipschitzWith B F) (hFn : ‖F‖≤B)
    (hd : η≤‖rectMean v L (fun x => F (p x))-(∫ y,F y ∂μ)‖) :
    ∃ F' : C(Y,ℂ), LipschitzWith 1 F' ∧ ‖F'‖≤1 ∧
      η/(B:ℝ)≤‖rectMean v L (fun x => F' (p x))-(∫ y,F' y ∂μ)‖ := by
  let z : ℂ := ((B:ℝ):ℂ)⁻¹
  have hBr : 0<(B:ℝ) := hB
  have hz : ‖z‖=(B:ℝ)⁻¹ := by simp [z]
  let F' : C(Y,ℂ) := z • F
  refine ⟨F',?_,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (z*F x) (z*F y)≤_
    simp only [dist_eq_norm,← mul_sub,norm_mul,hz]
    rw [← dist_eq_norm]
    calc
      _ ≤ (B:ℝ)⁻¹*((B:ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hFL.dist_le_mul x y) (by positivity)
      _ = (1:NNReal)*dist x y := by norm_num; field_simp
  · change ‖z • F‖≤1
    rw [norm_smul,hz]
    exact (mul_le_mul_of_nonneg_left hFn (by positivity)).trans_eq (inv_mul_cancel₀ hBr.ne')
  · change η/(B:ℝ)≤‖rectMean v L (fun x => z*F (p x))-(∫ y,z*F y ∂μ)‖
    rw [rectMean_smul,integral_const_mul,← mul_sub,norm_mul,hz]
    rw [div_eq_mul_inv,mul_comm]
    exact mul_le_mul_of_nonneg_left hd (by positivity)

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

open SquareInduction BoxPolynomialLines PolynomialLineCoefficients
open CorrectedBoxLeibman TriangularLatticeRecovery

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem comparable_integer_box
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A Z₀ : ℝ, 0<A ∧ 0<Z₀ ∧
      ∀ Z : ℝ, Z₀≤Z → ∀ a₀ : Fin v→ℤ, ∀ L : Fin v→ℕ,
      (∀ i,c₀*Z≤(L i:ℝ)) →
      (∀ i (k : ℕ),k<L i → |((a₀ i+(k:ℤ):ℤ):ℝ)|≤C₀*Z) →
      ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith B F ∧ ‖F‖≤B ∧
        η≤‖rectMean v L (fun x => F (QuotientGroup.mk (f (fun i => a₀ i+(x i:ℤ)))))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ a : PolynomialLineCoefficients.Grid v s→ℝ,
          (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f x)).toAdd) ∧
          (∀ I,s<totalDegree I → a I=0) ∧
          ∀ I,0<totalDegree I → circleNorm (a I)≤A/(Z^(totalDegree I)) := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  have hBr : 0<(B:ℝ) := hB
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_integer_box_unit c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ (η/(B:ℝ)) hc₀ hC₀ (div_pos hη hBr)
  refine ⟨U,A,Z₀,hA,hZ₀,?_⟩
  intro Z hZ a₀ L hL hloc f hf hd
  obtain ⟨F,hFL,hFn,hdisc⟩ := hd
  obtain ⟨F',hFL',hFn',hdisc'⟩ := normalized_rect_observable μ v L (fun x => QuotientGroup.mk (f (fun i => a₀ i+(x i:ℤ)))) B hB η F hFL hFn hdisc
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hat,hac⟩ := hprod Z hZ a₀ L hL hloc f hf ⟨F',hFL',hFn',hdisc'⟩
  refine ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hat,?_⟩
  intro I hI
  exact (le_div_iff₀ (pow_pos (hZ₀.trans_le hZ) _)).mpr (hac I hI)

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace ComparableBoxLeibman

 
def integerLength (lo hi : ℝ) : ℕ := (⌊hi⌋-⌈lo⌉+1).toNat

lemma integerCoord_bounds (lo hi : ℝ) (k : ℕ) (hk : k < integerLength lo hi) :
    lo≤((⌈lo⌉+(k:ℤ):ℤ):ℝ) ∧ ((⌈lo⌉+(k:ℤ):ℤ):ℝ)≤hi := by
  have hki : (k:ℤ)<⌊hi⌋-⌈lo⌉+1 := by
    dsimp [integerLength] at hk
    omega
  constructor
  · exact (Int.le_ceil lo).trans (by push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg _))
  · apply Int.le_floor.mp
    omega

lemma integerCoord_exists (lo hi : ℝ) (z : ℤ) (hlo : lo≤(z:ℝ)) (hhi : (z:ℝ)≤hi) :
    ∃ k : Fin (integerLength lo hi),⌈lo⌉+(k.val:ℤ)=z := by
  have hzlo := Int.ceil_le.mpr hlo
  have hzhi := Int.le_floor.mpr hhi
  have hn : 0≤z-⌈lo⌉ := sub_nonneg.mpr hzlo
  refine ⟨⟨(z-⌈lo⌉).toNat,?_⟩,?_⟩
  · dsimp [integerLength]
    exact (Int.toNat_lt_toNat (by omega)).mpr (by omega)
  · rw [Int.toNat_of_nonneg hn]
    omega

 
def integerBox (v : ℕ) (lo hi : Fin v→ℝ) : Finset (Fin v→ℤ) :=
  Finset.univ.image (fun x : (i : Fin v)→Fin (integerLength (lo i) (hi i)) =>
    fun i => ⌈lo i⌉+((x i).val:ℤ))

lemma mem_integerBox {v : ℕ} (lo hi : Fin v→ℝ) (z : Fin v→ℤ) :
    z∈integerBox v lo hi ↔ ∀ i,lo i≤(z i:ℝ) ∧ (z i:ℝ)≤hi i := by
  classical
  constructor
  · intro hz
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    exact fun i => integerCoord_bounds _ _ _ (x i).isLt
  · intro hz
    choose x hx using (fun i => integerCoord_exists (lo i) (hi i) (z i) (hz i).1 (hz i).2)
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,funext hx⟩

lemma integerBox_average (v : ℕ) (lo hi : Fin v→ℝ) (f : (Fin v→ℤ)→ℂ) :
    (𝔼 z∈integerBox v lo hi,f z)=
      rectMean v (fun i => integerLength (lo i) (hi i))
        (fun x => f (fun i => ⌈lo i⌉+(x i:ℤ))) := by
  classical
  rw [integerBox,Finset.expect_image,rectMean_eq_fin]
  intro x _ y _ hxy
  ext i
  have h := congrFun hxy i
  exact_mod_cast (add_left_cancel h)

lemma integerLength_lower (lo hi W : ℝ) (hW : 2≤W) (hside : W≤hi-lo) :
    W/2≤(integerLength lo hi:ℝ) := by
  have hfl := Int.lt_floor_add_one hi
  have hcl := Int.ceil_lt_add_one lo
  have hd : 0<(⌊hi⌋-⌈lo⌉+1:ℤ) := by
    have hh : (0:ℝ)<((⌊hi⌋:ℤ):ℝ)-((⌈lo⌉:ℤ):ℝ)+1 := by linarith
    exact_mod_cast hh
  have hc : (integerLength lo hi:ℝ)=((⌊hi⌋-⌈lo⌉+1:ℤ):ℝ) := by
    dsimp [integerLength]
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hd.le]
  rw [hc]
  push_cast
  linarith

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

open SquareInduction BoxPolynomialLines PolynomialLineCoefficients
open CorrectedBoxLeibman TriangularLatticeRecovery

local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem comparable_real_box
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A Z₀ : ℝ, 0<A ∧ 0<Z₀ ∧
      ∀ Z : ℝ, Z₀≤Z → ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*Z≤hi i-lo i) →
      (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) →
      ∀ f : (Fin v→ℤ)→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith B F ∧ ‖F‖≤B ∧
        η≤‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk (f x)))-(∫ y,F y ∂μ)‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) ∧
        ∃ a : PolynomialLineCoefficients.Grid v s→ℝ,
          (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f x)).toAdd) ∧
          (∀ I,s<totalDegree I → a I=0) ∧
          ∀ I,0<totalDegree I → circleNorm (a I)≤A/(Z^(totalDegree I)) := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,Z₁,hA,hZ₁,hprod⟩ := comparable_integer_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v (c₀/2) C₀ B η (by positivity) hC₀ hB hη
  refine ⟨U,A,max Z₁ (2/c₀),hA,lt_of_lt_of_le hZ₁ (le_max_left _ _),?_⟩
  intro Z hZ lo hi hside hloc f hf hd
  have hZZ : Z₁≤Z := (le_max_left _ _).trans hZ
  have hbig : 2≤c₀*Z := by
    have hz := (le_max_right Z₁ (2/c₀)).trans hZ
    simpa [mul_comm] using (div_le_iff₀ hc₀).mp hz
  have hlength : ∀ i,(c₀/2)*Z≤(integerLength (lo i) (hi i):ℝ) := by
    intro i
    convert integerLength_lower (lo i) (hi i) (c₀*Z) hbig (hside i) using 1; ring
  have hlocation : ∀ i (k : ℕ),k < integerLength (lo i) (hi i) →
      |((⌈lo i⌉+(k:ℤ):ℤ):ℝ)|≤C₀*Z := by
    intro i k hk
    have hb := integerCoord_bounds (lo i) (hi i) k hk
    exact abs_le.mpr ⟨by nlinarith [hloc i],hb.2.trans (hloc i).2⟩
  apply hprod Z hZZ (fun i => ⌈lo i⌉) (fun i => integerLength (lo i) (hi i)) hlength hlocation f hf
  obtain ⟨F,hFL,hFn,hdisc⟩ := hd
  refine ⟨F,hFL,hFn,?_⟩
  simpa only [integerBox_average] using hdisc

end ComparableBoxLeibman

end
end
end
end
end

end OAI
