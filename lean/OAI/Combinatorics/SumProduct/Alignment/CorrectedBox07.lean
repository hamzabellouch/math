import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ComparableBox02
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
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients

 
lemma gridEval_integer_injective {v s : ℕ} {a b : Grid v s→ℝ}
    (hab : ∀ x : Fin v→ℤ,gridEval a (fun i => (x i:ℝ))=gridEval b (fun i => (x i:ℝ))) : a=b := by
  classical
  let L := v*s+1
  have hL : 0<L := by dsimp [L]; omega
  have hD (e : Grid v s) : (gridExponent e).sum (fun _ k => k)≤v*s := by
    rw [gridExponent_degree]
    exact grid_totalDegree_bound e
  let Q := (Finset.univ : Finset (Fin v→Fin L))
  have hden : (v*s:ℕ)/(L:ℚ≥0)<(Q.card:ℚ≥0)/(L:ℚ≥0)^v := by
    have hLp : (0:ℚ≥0)<L := Nat.cast_pos.mpr hL
    have hpow : (L:ℚ≥0)^v≠0 := ne_of_gt (pow_pos hLp _)
    simp only [Q,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,div_self hpow]
    apply (div_lt_one hLp).mpr
    exact_mod_cast (show v*s<L by dsimp [L]; omega)
  obtain ⟨B,hB,w,hw⟩ := dense_grid_integer_weights gridExponent (gridExponent_injective v s)
    (v*s) hD L Q hden
  have he (q : Q) : (∑ e,a e*(gridMonomial gridExponent q.val e:ℝ))=
      ∑ e,b e*(gridMonomial gridExponent q.val e:ℝ) := by
    simpa only [gridEval,gridMonomial_eq_prod,Int.cast_natCast] using hab (fun i => ((q.val i).val:ℤ))
  funext i
  have ha := TriangularLatticeRecovery.reconstruct_slice (fun _ : Grid v s => 0)
    (fun q : Q => gridMonomial gridExponent q.val) w B hw a 0 i rfl
  have hb := TriangularLatticeRecovery.reconstruct_slice (fun _ : Grid v s => 0)
    (fun q : Q => gridMonomial gridExponent q.val) w B hw b 0 i rfl
  simp only [ite_true,he] at ha hb
  have hp : (B:ℝ)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt hB)
  exact (mul_left_cancel₀ hp) (ha.symm.trans hb)

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction BoxPolynomialLines PolynomialLineCoefficients CorrectedBoxLeibman TriangularLatticeRecovery
open Filter
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem haar_limit_of_horizontal_irrationality
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (f : ℕ→(Fin v→ℤ)→G) (hf : ∀ N,LeibmanSquare.Polynomial H 0 (f N))
    (hirr : ∀ ξ : G→*Multiplicative ℝ, ξ≠1 → Continuous ξ →
      (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∃ a : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ N x,gridEval (a N) (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) ∧
        ∃ I,0 < totalDegree I ∧
          Tendsto (fun N => circleNorm (a N I)*(N:ℝ)^(totalDegree I)) atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(N:ℝ)≤hi i-lo i) →
      (∀ i,-C₀*(N:ℝ)≤lo i ∧ hi i≤C₀*(N:ℝ)) →
      ∀ F : C(G⧸Γ,ℂ),LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk (f N x)))-(∫ y,F y ∂μ)‖<η := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  intro η hη
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_real_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ B η hc₀ hC₀ hB hη
  have hlarge (ξ : G→*Multiplicative ℝ) : ∀ᶠ N : ℕ in atTop,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ A<circleNorm (a I)*(N:ℝ)^(totalDegree I) := by
    by_cases hc : ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z)
    · obtain ⟨a,ha,I,hI,hlim⟩ := hirr ξ hc.1 hc.2.1 hc.2.2
      filter_upwards [hlim.eventually_gt_atTop A] with N hN
      intro _ _ _ b hb
      have hab : a N=b := gridEval_integer_injective (fun x => (ha N x).trans (hb x).symm)
      exact ⟨I,hI,by simpa only [hab] using hN⟩
    · exact Filter.Eventually.of_forall (by intro N hne hcont hint; exact (hc ⟨hne,hcont,hint⟩).elim)
  have hall : ∀ᶠ N : ℕ in atTop,∀ ξ∈U,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ A<circleNorm (a I)*(N:ℝ)^(totalDegree I) :=
    (Filter.eventually_all_finset U).mpr (fun ξ _ => hlarge ξ)
  have hNlarge : ∀ᶠ N : ℕ in atTop,Z₀≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop Z₀
  filter_upwards [hall,hNlarge] with N hN hNZ
  intro lo hi hside hloc F hFL hFn
  by_contra hbad
  have hdisc : η≤‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk (f N x)))-(∫ y,F y ∂μ)‖ := le_of_not_gt hbad
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,a,ha,hat,hac⟩ := hprod (N:ℝ) hNZ lo hi hside hloc (f N) (hf N) ⟨F,hFL,hFn,hdisc⟩
  obtain ⟨I,hI,hIA⟩ := hN ξ hξ hξne hξc hξΓ a ha
  have hpow : 0<(N:ℝ)^(totalDegree I) := pow_pos (hZ₀.trans_le hNZ) _
  have hbnd := (le_div_iff₀ hpow).mp (hac I hI)
  exact (not_lt_of_ge hbnd) hIA

end ComparableBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace CorrectedBoxLeibman
open PolynomialLineCoefficients TriangularLatticeRecovery

lemma gridEval_mul {v s : ℕ} (a : Grid v s→ℝ) (D : ℝ) (x : Fin v→ℝ) :
    gridEval (fun I => D*a I) x=D*gridEval a x := by
  simp only [gridEval,Finset.mul_sum,mul_assoc]

lemma gridTranslate_mul {v s : ℕ} (a : Grid v s→ℝ) (D : ℝ) (r : Fin v→ℤ) :
    gridTranslate (fun I => D*a I) r=(fun I => D*gridTranslate a r I) := by
  funext I
  simp only [gridTranslate,Finset.mul_sum,mul_assoc]

lemma gridTranslate_cancel {v s : ℕ} (a : Grid v s→ℝ) (r : Fin v→ℤ) :
    gridTranslate (gridTranslate a r) (fun i => -r i)=a := by
  apply gridEval_integer_injective
  intro x
  rw [gridTranslate_eval,gridTranslate_eval]
  congr 1
  funext i
  simp

 
def gridDilate {v s : ℕ} (d : ℕ) (a : Grid v s→ℝ) (I : Grid v s) : ℝ :=
  (d:ℝ)^(totalDegree I)*a I

lemma gridDilate_eval {v s : ℕ} (d : ℕ) (a : Grid v s→ℝ) (x : Fin v→ℝ) :
    gridEval (gridDilate d a) x=gridEval a (fun i => (d:ℝ)*x i) := by
  simp only [gridEval,gridDilate]
  apply Finset.sum_congr rfl
  intro I _
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,totalDegree]
  ring

lemma gridAffine_unique {v s : ℕ} (d : ℕ) (r : Fin v→ℤ) (a b : Grid v s→ℝ)
    (hab : ∀ x : Fin v→ℤ,gridEval b (fun i => (x i:ℝ))=
      gridEval a (fun i => ((r i+(d:ℤ)*x i:ℤ):ℝ))) :
    b=gridDilate d (gridTranslate a r) := by
  apply gridEval_integer_injective
  intro x
  rw [gridDilate_eval,gridTranslate_eval,hab]
  congr 1
  funext i
  push_cast
  ring

 

theorem gridAffine_recover_bound {v s : ℕ} (d : ℕ) (hd : 0<d)
    (r : Fin v→ℤ) (a b : Grid v s→ℝ) (Z C A : ℝ)
    (hZ : 0≤Z) (hC : 1≤C) (hA : 0≤A)
    (hr : ∀ i, |(r i:ℝ)|≤C*Z)
    (hab : ∀ x : Fin v→ℤ,gridEval b (fun i => (x i:ℝ))=
      gridEval a (fun i => ((r i+(d:ℤ)*x i:ℤ):ℝ)))
    (hb : ∀ I,0<totalDegree I → circleNorm (b I)*Z^(totalDegree I)≤A) :
    ∀ I,0<totalDegree I →
      circleNorm ((d:ℝ)^(v*s)*a I)*Z^(totalDegree I)≤
        ((s+1:ℕ)^v:ℝ)*(2^s*C^s)^v*((d:ℝ)^(v*s)*A) := by
  have hab' := gridAffine_unique d r a b hab
  let a' : Grid v s→ℝ := fun I => (d:ℝ)^(v*s-totalDegree I)*b I
  have ha' : a'=(fun I => (d:ℝ)^(v*s)*gridTranslate a r I) := by
    funext I
    dsimp [a']
    rw [hab',gridDilate,← mul_assoc,← pow_add,Nat.sub_add_cancel (grid_totalDegree_bound I)]
  have hacancel : gridTranslate a' (fun i => -r i)=(fun I => (d:ℝ)^(v*s)*a I) := by
    rw [ha',gridTranslate_mul,gridTranslate_cancel]
  have ha'bound : ∀ I,0<totalDegree I →
      circleNorm (a' I)*Z^(totalDegree I)≤(d:ℝ)^(v*s)*A := by
    intro I hI
    have hc := circleNorm_nat_mul (d^(v*s-totalDegree I)) (b I)
    push_cast at hc
    calc
      _ ≤ ((d:ℝ)^(v*s-totalDegree I)*circleNorm (b I))*Z^(totalDegree I) :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg hZ _)
      _ = (d:ℝ)^(v*s-totalDegree I)*(circleNorm (b I)*Z^(totalDegree I)) := by ring
      _ ≤ (d:ℝ)^(v*s-totalDegree I)*A :=
        mul_le_mul_of_nonneg_left (hb I hI) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by exact_mod_cast hd : (1:ℝ)≤d) (Nat.sub_le _ _)) hA
  intro I hI
  have hrec := gridTranslate_bound a' (fun i => -r i) Z C ((d:ℝ)^(v*s)*A)
    hZ hC (by positivity) (by intro i; simpa using hr i) ha'bound I hI
  simpa only [hacancel] using hrec

end CorrectedBoxLeibman
end
end
 

 
section
noncomputable section
open scoped BigOperators Topology
namespace ComparableBoxLeibman
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
open SquareInduction BoxPolynomialLines PolynomialLineCoefficients CorrectedBoxLeibman TriangularLatticeRecovery
open Filter
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1)=⊥)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
local instance progressionHaarTopology : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem haar_limit_fixed_progression
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (f : ℕ→(Fin v→ℤ)→G) (hf : ∀ N,LeibmanSquare.Polynomial H 0 (f N))
    (hirr : ∀ ξ : G→*Multiplicative ℝ, ξ≠1 → Continuous ξ →
      (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∃ a : ℕ→PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ N x,gridEval (a N) (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) ∧
        ∃ I,0 < totalDegree I ∧
          Tendsto (fun N => circleNorm (a N I)*(N:ℝ)^(totalDegree I)) atTop atTop)
    (c₀ C₀ : ℝ) (B : NNReal) (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B)
    (d₀ : ℕ) (hd₀ : 0<d₀) (r : Fin v→ℤ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∀ η : ℝ,0<η → ∀ᶠ N : ℕ in atTop,
      ∀ lo hi : Fin v→ℝ,
      (∀ i,c₀*(N:ℝ)≤hi i-lo i) →
      (∀ i,-C₀*(N:ℝ)≤lo i ∧ hi i≤C₀*(N:ℝ)) →
      ∀ F : C(G⧸Γ,ℂ),LipschitzWith B F → ‖F‖≤B →
        ‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
          (f N (fun i => r i+(d₀:ℤ)*x i))))-(∫ y,F y ∂μ)‖<η := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  intro η hη
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_real_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop μ v c₀ C₀ B η hc₀ hC₀ hB hη
  let D : ℕ := d₀^(v*s)
  have hD : 0<D := pow_pos hd₀ _
  let C : ℝ := 1+∑ i,|(r i:ℝ)|
  have hC : 1≤C := by dsimp [C]; linarith [Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => abs_nonneg (r i:ℝ))]
  have hrC (i : Fin v) : |(r i:ℝ)|≤C := by
    have hh := Finset.single_le_sum (f := fun i : Fin v => |(r i:ℝ)|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [C]
    linarith
  let E : ℝ := ((s+1:ℕ)^v:ℝ)*(2^s*C^s)^v*((d₀:ℝ)^(v*s)*A)
  have hlarge (ξ : G→*Multiplicative ℝ) : ∀ᶠ N : ℕ in atTop,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ E<circleNorm ((d₀:ℝ)^(v*s)*a I)*(N:ℝ)^(totalDegree I) := by
    by_cases hc : ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z)
    · have hΞΓ : ∀ g∈Γ,∃ z : ℤ,((ξ^D) g).toAdd=z := by
        intro g hg
        obtain ⟨z,hz⟩ := hc.2.2 g hg
        refine ⟨(D:ℤ)*z,?_⟩
        rw [character_pow_toAdd,hz]
        simp
      obtain ⟨a,ha,I,hI,hlim⟩ := hirr (ξ^D) (character_pow_ne ξ hc.1 D hD) (hc.2.1.pow D) hΞΓ
      filter_upwards [hlim.eventually_gt_atTop E] with N hN
      intro _ _ _ b hb
      have hab : a N=(fun I => (d₀:ℝ)^(v*s)*b I) := by
        apply gridEval_integer_injective
        intro x
        rw [ha,gridEval_mul,hb,character_pow_toAdd]
        simp [D]
      exact ⟨I,hI,by simpa only [hab] using hN⟩
    · exact Filter.Eventually.of_forall (by intro N hne hcont hint; exact (hc ⟨hne,hcont,hint⟩).elim)
  have hall : ∀ᶠ N : ℕ in atTop,∀ ξ∈U,
      ξ≠1 → Continuous ξ → (∀ g∈Γ,∃ z : ℤ,(ξ g).toAdd=z) →
      ∀ a : PolynomialLineCoefficients.Grid v s→ℝ,
        (∀ x,gridEval a (fun i => (x i:ℝ))=(ξ (f N x)).toAdd) →
        ∃ I,0<totalDegree I ∧ E<circleNorm ((d₀:ℝ)^(v*s)*a I)*(N:ℝ)^(totalDegree I) :=
    (Filter.eventually_all_finset U).mpr (fun ξ _ => hlarge ξ)
  have hNlarge : ∀ᶠ N : ℕ in atTop,max 1 Z₀≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (max 1 Z₀)
  let φ : (Fin v→ℤ)→+(Fin v→ℤ) :=
    { toFun := fun x i => (d₀:ℤ)*x i
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp [mul_add] }
  filter_upwards [hall,hNlarge] with N hN hNZ
  have hNZ₀ : Z₀≤(N:ℝ) := (le_max_right _ _).trans hNZ
  have hN1 : 1≤(N:ℝ) := (le_max_left _ _).trans hNZ
  intro lo hi hside hloc F hFL hFn
  by_contra hbad
  have hdisc : η≤‖(𝔼 x∈integerBox v lo hi,F (QuotientGroup.mk
      (f N (fun i => r i+(d₀:ℤ)*x i))))-(∫ y,F y ∂μ)‖ := le_of_not_gt hbad
  have hgf := polynomial_affine H (hf N) φ r
  obtain ⟨ξ,hξ,hξne,hξc,hξΓ,b,hb,hbt,hbc⟩ := hprod (N:ℝ) hNZ₀ lo hi hside hloc
    (fun x => f N (r+φ x)) hgf ⟨F,hFL,hFn,hdisc⟩
  obtain ⟨a,ha⟩ := character_grid_expansion H s hs (hf N) ξ
  have hab : ∀ x : Fin v→ℤ,gridEval b (fun i => (x i:ℝ))=
      gridEval a (fun i => ((r i+(d₀:ℤ)*x i:ℤ):ℝ)) := by
    intro x
    rw [hb,ha]
    rfl
  have hbnd := gridAffine_recover_bound d₀ hd₀ r a b (N:ℝ) C A (Nat.cast_nonneg _) hC hA.le
    (fun i => (hrC i).trans (le_mul_of_one_le_right (zero_le_one.trans hC) hN1)) hab
    (fun I hI => (le_div_iff₀ (pow_pos (hZ₀.trans_le hNZ₀) _)).mp (hbc I hI))
  obtain ⟨I,hI,hIE⟩ := hN ξ hξ hξne hξc hξΓ a ha
  exact (not_lt_of_ge (hbnd I hI)) hIE

end ComparableBoxLeibman

end
end
end
end
end

end OAI
