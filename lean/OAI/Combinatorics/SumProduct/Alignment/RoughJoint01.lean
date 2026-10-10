import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughSampling02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
end

 
end

section
 

 

noncomputable section
open scoped BigOperators

namespace RoughAnalyticExtraction
open FinitePieceAverages RoughSamplingWeights ComparableBoxLeibman
open CorrectedBoxLeibman PolynomialLineCoefficients

lemma mean_eq_expect {α : Type*} (s : Finset α) (f : α → ℂ) :
    mean s f = 𝔼 x ∈ s, f x := by
  rw [mean, Finset.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

lemma boxIndices_eq_halfOpen {v : ℕ} (lo hi : Fin v → ℝ) :
    boxIndices lo hi (fun _ => 0) 1 = halfOpenBox v lo hi := by
  ext x
  rw [mem_boxIndices _ _ _ _ zero_lt_one, mem_halfOpenBox]
  simp only [zero_add, one_mul]

lemma physicalResidueBox_mod {v : ℕ} (lo hi : Fin v → ℝ) (b : Fin v → ℤ)
    (p : ℕ) :
    physicalResidueBox lo hi (fun i => b i % p) p = physicalResidueBox lo hi b p := by
  classical
  unfold physicalResidueBox
  congr 1
  funext x
  apply propext
  simp only [Int.ModEq, Int.emod_emod]

lemma physicalResidueBox_one {v : ℕ} (lo hi : Fin v → ℝ) :
    physicalResidueBox lo hi (fun _ => 0) 1 = boxIndices lo hi (fun _ => 0) 1 := by
  classical
  simp [physicalResidueBox, Int.ModEq]

lemma halfOpen_bounds_pointwise {v : ℕ} (lo hi : Fin v → ℝ) (c C Z : ℝ)
    (hc : 0 < c) (hZ : 2/c ≤ Z)
    (hside : ∀ i, c*Z ≤ hi i-lo i)
    (hbox : ∀ i, -C*Z ≤ lo i ∧ hi i ≤ C*Z) :
    (∀ i, (c/2)*Z ≤ ((⌈hi i⌉:ℝ)-1)-lo i) ∧
    (∀ i, -C*Z ≤ lo i ∧ ((⌈hi i⌉:ℝ)-1) ≤ C*Z) := by
  have hcZ : 2 ≤ c*Z := by
    have := (div_le_iff₀ hc).mp hZ
    nlinarith
  constructor
  · intro i
    have := Int.le_ceil (hi i)
    have := hside i
    nlinarith
  · intro i
    refine ⟨(hbox i).1, ?_⟩
    have := Int.ceil_lt_add_one (hi i)
    have := (hbox i).2
    linarith

 

def integerDilation (v p : ℕ) : (Fin v → ℤ) →+ (Fin v → ℤ) where
  toFun x := fun i => (p:ℤ)*x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

lemma polynomial_affine {G : Type*} [Group G] (H : CubeFaces.Filtration G)
    {v : ℕ} {f : (Fin v → ℤ) → G} (hf : LeibmanSquare.Polynomial H 0 f)
    (u : Fin v → ℤ) (p : ℕ) :
    LeibmanSquare.Polynomial H 0 (fun x => f (integerAffine u p x)) :=
  LeibmanSquare.polynomial_affine H hf (integerDilation v p) u

 

def CharacterObstruction {G : Type*} [Group G] [TopologicalSpace G] {v s : ℕ}
    (Γ : Subgroup G) (f : (Fin v → ℤ) → G)
    (ξ : G →* Multiplicative ℝ) (u : Fin v → ℤ) (p : ℕ) (Z A : ℝ) : Prop :=
  ξ ≠ 1 ∧ Continuous ξ ∧ (∀ g ∈ Γ, ∃ z : ℤ, (ξ g).toAdd = z) ∧
    ∃ θ : PolynomialLineCoefficients.Grid v s → ℝ,
      (∀ x, gridEval θ (fun i => (x i:ℝ)) = (ξ (f x)).toAdd) ∧
      (∀ I, s < totalDegree I → θ I = 0) ∧
      ∀ I, 0 < totalDegree I →
        TriangularLatticeRecovery.circleNorm (gridDilate p (gridTranslate θ u) I)
          ≤ A * ((p:ℝ)/Z) ^ totalDegree I

section Nilmanifold
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs : H.level (s+1) = ⊥)
variable (q : ℕ → ℕ) (hqbound : ∀ k, q k ≤ t+d)
variable (hq : ∀ k (g : G), g ∈ H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i = 0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
variable [MeasurableSpace (G⧸Γ)]
variable [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace = QuotientGroup.instTopologicalSpace Γ)
local instance : TopologicalSpace (G⧸Γ) := mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem residue_haar_character
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 0 < B) (hη : 0 < η) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G →* Multiplicative ℝ), ∃ A T : ℝ, 0 < A ∧ 1 ≤ T ∧
      ∀ (Z : ℝ) (p : ℕ), 0 < p → T ≤ Z/p →
      ∀ (lo hi : Fin v → ℝ) (u : Fin v → ℤ),
      (∀ i, 0 ≤ u i ∧ u i < p) →
      (∀ i, c₀*Z ≤ hi i-lo i) →
      (∀ i, -C₀*Z ≤ lo i ∧ hi i ≤ C₀*Z) →
      ∀ f : (Fin v → ℤ) → G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith B F ∧ ‖F‖ ≤ B ∧
        η ≤ ‖mean (physicalResidueBox lo hi u p) (fun x => F (QuotientGroup.mk (f x))) -
          ∫ y, F y ∂μ‖) →
      ∃ ξ ∈ U, CharacterObstruction (s:=s) Γ f ξ u p Z A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,Z₀,hA,hZ₀,hprod⟩ := comparable_real_box c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop
    μ v (c₀/2) (C₀+1) B η (by positivity) (by positivity) hB hη
  let T := max 1 (max (2/c₀) Z₀)
  refine ⟨U,A,T,hA,le_max_left _ _,?_⟩
  intro Z p hp hZT lo hi u hu hside hbox f hf hbad
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hscale : 1 ≤ Z/p := (le_max_left _ _).trans hZT
  have hpZ : (p:ℝ) ≤ Z := by simpa using (le_div_iff₀ hpR).mp hscale
  have hZ : 0 < Z := hpR.trans_le hpZ
  have hscale₂ : 2/c₀ ≤ Z/p := (le_max_of_le_right (le_max_left _ _)).trans hZT
  have hscale₀ : Z₀ ≤ Z/p := (le_max_of_le_right (le_max_right _ _)).trans hZT
  have hg := rescaled_geometry lo hi u p hp Z C₀ c₀ hpZ hC₀.le
    (fun i => ⟨(hu i).1,(hu i).2.le⟩) (by simpa only [neg_mul] using hbox) hside
  have hb := halfOpen_bounds_pointwise (rescaledEndpoint lo u p) (rescaledEndpoint hi u p)
    c₀ (C₀+1) (Z/p) hc₀ hscale₂ (fun i => (hg i).2.2)
    (fun i => ⟨(hg i).1,(hg i).2.1⟩)
  obtain ⟨F,hFL,hFB,hFD⟩ := hbad
  have hbad' : η ≤ ‖(𝔼 x ∈ integerBox v (rescaledEndpoint lo u p)
      (fun i => (⌈rescaledEndpoint hi u p i⌉:ℝ)-1),
      F (QuotientGroup.mk (f (integerAffine u p x)))) - ∫ y, F y ∂μ‖ := by
    rw [residue_mean lo hi u p hp, boxIndices_eq_halfOpen, mean_eq_expect] at hFD
    exact hFD
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,a,ha,hat,hab⟩ := hprod (Z/p) hscale₀
    (rescaledEndpoint lo u p) (fun i => (⌈rescaledEndpoint hi u p i⌉:ℝ)-1)
    hb.1 hb.2 (fun x => f (integerAffine u p x)) (polynomial_affine H hf u p)
    ⟨F,hFL,hFB,hbad'⟩
  obtain ⟨θ,hθ⟩ := character_grid_expansion H s hs hf ξ
  have haff : a = gridDilate p (gridTranslate θ u) :=
    gridAffine_unique p u θ a (fun x => (ha x).trans (hθ (integerAffine u p x)).symm)
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,θ,hθ,?_,?_⟩
  · apply grid_totalDegree (f:=fun x => (ξ (f x)).toAdd) _ θ hθ
    intro x q
    exact LeibmanSquare.character_polynomial H s hs
      (LeibmanSquare.polynomial_integer_line H hf x q) ξ
  · intro I hI
    rw [← haff]
    convert hab I hI using 1
    conv_rhs => rw [div_eq_mul_inv, ← inv_pow, inv_div]

include hsk h0 h1 hs hqbound hq hΓ htop in
 

theorem discrepancy_character
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 0 < B) (hη : 0 < η) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G →* Multiplicative ℝ), ∃ A T : ℝ, 0 < A ∧ 1 ≤ T ∧
      ∀ (Z : ℝ) (k : ℕ), 0 < k → T ≤ Z/k →
      ∀ (lo hi : Fin v → ℝ) (b : Fin v → ℤ),
      (∀ i, c₀*Z ≤ hi i-lo i) →
      (∀ i, -C₀*Z ≤ lo i ∧ hi i ≤ C₀*Z) →
      ∀ f : (Fin v → ℤ) → G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith B F ∧ ‖F‖ ≤ B ∧
        η ≤ ‖mean (boxIndices lo hi (fun _ => 0) 1)
            (fun x => F (QuotientGroup.mk (f x))) -
          mean (physicalResidueBox lo hi b k) (fun x => F (QuotientGroup.mk (f x)))‖) →
      ∃ p : ℕ, ∃ u : Fin v → ℤ, (p = 1 ∨ p = k) ∧
        (∀ i, 0 ≤ u i ∧ u i < p) ∧
        ∃ ξ ∈ U, CharacterObstruction (s:=s) Γ f ξ u p Z A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,A,T,hA,hT,hprod⟩ := residue_haar_character c hsk H h0 h1 s hs q hqbound hq Γ hΓ htop
    μ v c₀ C₀ B (η/2) hc₀ hC₀ hB (by positivity)
  refine ⟨U,A,T,hA,hT,?_⟩
  intro Z k hk hTZ lo hi b hside hbox f hf hbad
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hZ : 0 < Z := by
    have hh := (le_div_iff₀ hkR).mp (hT.trans hTZ)
    nlinarith
  have hTZ' : T ≤ Z/(1:ℕ) := by
    simp only [Nat.cast_one, div_one]
    exact hTZ.trans (div_le_self hZ.le hk1)
  obtain ⟨F,hFL,hFB,hFD⟩ := hbad
  let a := mean (boxIndices lo hi (fun _ => 0) 1) (fun x => F (QuotientGroup.mk (f x)))
  let b' := mean (physicalResidueBox lo hi b k) (fun x => F (QuotientGroup.mk (f x)))
  let h := ∫ y, F y ∂μ
  have htriangle : ‖a-b'‖ ≤ ‖a-h‖ + ‖b'-h‖ := by
    calc
      ‖a-b'‖ = ‖(a-h)+(h-b')‖ := by congr 1; ring
      _ ≤ ‖a-h‖ + ‖h-b'‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev h b']
  by_cases ha : η/2 ≤ ‖a-h‖
  · refine ⟨1,fun _ => 0,Or.inl rfl,(by intro i; simp),?_⟩
    apply hprod Z 1 zero_lt_one hTZ' lo hi (fun _ => 0) (by intro i; simp) hside hbox f hf
    refine ⟨F,hFL,hFB,?_⟩
    simpa only [physicalResidueBox_one] using ha
  · have hb : η/2 ≤ ‖b'-h‖ := by
      change η ≤ ‖a-b'‖ at hFD
      linarith [lt_of_not_ge ha]
    let u : Fin v → ℤ := fun i => b i % k
    have hu : ∀ i, 0 ≤ u i ∧ u i < k := by
      intro i
      exact ⟨Int.emod_nonneg _ (by exact_mod_cast hk.ne'),
        Int.emod_lt_of_pos _ (by exact_mod_cast hk)⟩
    refine ⟨k,u,Or.inr rfl,hu,?_⟩
    apply hprod Z k hk hTZ lo hi u hu hside hbox f hf
    refine ⟨F,hFL,hFB,?_⟩
    simpa only [u,physicalResidueBox_mod] using hb

end Nilmanifold
end RoughAnalyticExtraction

end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RoughJointCoefficients
open _root_.Polynomial _root_.OAI.Polynomial CorrectedBoxLeibman PolynomialLineCoefficients
open RoughAnalyticExtraction TriangularLatticeRecovery

 
def timeCoefficient {v s : ℕ} (a : PolynomialLineCoefficients.Grid (v+1) s → ℝ)
    (I : PolynomialLineCoefficients.Grid v s) : ℝ[X] :=
  ∑ j : Fin (s+1), C (a (Fin.cons j I)) * X^j.val

lemma timeCoefficient_degree {v s : ℕ} (a : PolynomialLineCoefficients.Grid (v+1) s → ℝ)
    (I : PolynomialLineCoefficients.Grid v s) : (timeCoefficient a I).natDegree ≤ s := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_C_mul_le _ _).trans (by simpa using Nat.le_of_lt_succ j.isLt)

lemma gridEval_timeCoefficient {v s : ℕ}
    (a : PolynomialLineCoefficients.Grid (v+1) s → ℝ) (z : ℝ) (x : Fin v → ℝ) :
    gridEval (fun I => (timeCoefficient a I).eval z) x =
      gridEval a (Fin.cons z x) := by
  classical
  simp only [gridEval,timeCoefficient,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (v+1) => Fin (s+1)))
  intro xj
  change (a (Fin.cons xj.1 xj.2) * z^xj.1.val) * (∏ i, x i^(xj.2 i).val) =
    a (Fin.cons xj.1 xj.2) * ∏ i, ((Fin.cons z x : Fin (v+1) → ℝ) i)^((Fin.cons xj.1 xj.2 : Fin (v+1) → Fin (s+1)) i).val
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

 
def spatialEmbedding (v : ℕ) : (Fin v → ℤ) →+ (Fin (v+1) → ℤ) where
  toFun x := Fin.cons 0 x
  map_zero' := by ext i; exact Fin.cases (by simp) (fun _ => by simp) i
  map_add' x y := by ext i; exact Fin.cases (by simp) (fun _ => by simp) i

lemma fibre_polynomial {G : Type*} [Group G] (H : CubeFaces.Filtration G)
    {v : ℕ} {f : (Fin (v+1) → ℤ) → G} (hf : LeibmanSquare.Polynomial H 0 f) (z : ℤ) :
    LeibmanSquare.Polynomial H 0 (fun x => f (Fin.cons z x)) := by
  have h := LeibmanSquare.polynomial_affine H hf (spatialEmbedding v) (Fin.cons z (fun _ => 0))
  convert h using 1
  funext x
  congr 1
  ext i
  exact Fin.cases (by simp [spatialEmbedding]) (fun j => by simp [spatialEmbedding]) i

 

theorem joint_character_coefficients {G : Type*} [Group G]
    (H : CubeFaces.Filtration G) (s : ℕ) (hs : H.level (s+1) = ⊥)
    {v : ℕ} {f : (Fin (v+1) → ℤ) → G} (hf : LeibmanSquare.Polynomial H 0 f)
    (ξ : G →* Multiplicative ℝ) :
    ∃ θ : PolynomialLineCoefficients.Grid v s → ℝ[X],
      (∀ I, (θ I).natDegree ≤ s) ∧
      ∀ z : ℤ, ∀ x : Fin v → ℤ,
        gridEval (fun I => (θ I).eval (z:ℝ)) (fun i => (x i:ℝ)) =
          (ξ (f (Fin.cons z x))).toAdd := by
  obtain ⟨a,ha⟩ := character_grid_expansion H s hs hf ξ
  refine ⟨timeCoefficient a, timeCoefficient_degree a,?_⟩
  intro z x
  rw [gridEval_timeCoefficient]
  convert ha (Fin.cons z x) using 2
  ext i
  exact Fin.cases rfl (fun _ => rfl) i

lemma obstruction_on_coefficients {G : Type*} [Group G] [TopologicalSpace G]
    {v s : ℕ} {Γ : Subgroup G} {f : (Fin v → ℤ) → G}
    {ξ : G →* Multiplicative ℝ} {u : Fin v → ℤ} {p : ℕ} {Z A : ℝ}
    (h : CharacterObstruction (s:=s) Γ f ξ u p Z A)
    (a : PolynomialLineCoefficients.Grid v s → ℝ)
    (ha : ∀ x,gridEval a (fun i => (x i:ℝ)) = (ξ (f x)).toAdd) :
    ∀ I,0 < totalDegree I →
      circleNorm (gridDilate p (gridTranslate a u) I) ≤ A*((p:ℝ)/Z)^totalDegree I := by
  obtain ⟨_,_,_,a',ha',_,hb⟩ := h
  have he : a = a' := gridEval_integer_injective (fun x => (ha x).trans (ha' x).symm)
  simpa only [he] using hb

@[simp] lemma translationMatrix_self {v s : ℕ} (u : Fin v → ℤ)
    (I : PolynomialLineCoefficients.Grid v s) : translationMatrix u I I = 1 := by
  unfold translationMatrix
  apply Finset.prod_eq_one
  intro k hk
  unfold translationEntry
  rw [coeff_X_add_C_pow]
  simp

lemma translationMatrix_eq_zero_of_degree_le {v s : ℕ} (u : Fin v → ℤ)
    (I J : PolynomialLineCoefficients.Grid v s) (hne : I ≠ J)
    (hdeg : totalDegree J ≤ totalDegree I) : translationMatrix u I J = 0 := by
  by_contra h
  have hle := translationMatrix_le u I J h
  have heq : ∀ i, (I i).val = (J i).val := by
    have heqs : (∑ i, (I i).val) = ∑ i, (J i).val :=
      le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) hdeg
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp heqs i (Finset.mem_univ i)
  apply hne
  ext i
  exact heq i

 

lemma gridTranslate_peeling {v s : ℕ} (u : Fin v → ℤ)
    (a : PolynomialLineCoefficients.Grid v s → ℝ) (I : PolynomialLineCoefficients.Grid v s) :
    gridTranslate a u I = a I +
      ∑ J ∈ Finset.univ.filter (fun J => totalDegree I < totalDegree J),
        (translationMatrix u I J:ℝ)*a J := by
  classical
  rw [gridTranslate, ← Finset.sum_erase_add (s:=Finset.univ) _ (Finset.mem_univ I)]
  rw [translationMatrix_self,Int.cast_one,mul_one,add_comm]
  congr 1
  rw [Finset.sum_filter]
  calc
    _ = ∑ J ∈ Finset.univ.erase I,
        if totalDegree I < totalDegree J then (translationMatrix u I J:ℝ)*a J else 0 := by
      apply Finset.sum_congr rfl
      intro J hJ
      have hJI : I≠J := by simpa [eq_comm] using (Finset.mem_erase.mp hJ).1
      by_cases hdeg : totalDegree I < totalDegree J
      · simp only [hdeg,ite_eq_left,mul_comm]
      · simp [hdeg,translationMatrix_eq_zero_of_degree_le u I J hJI (by omega)]
    _ = _ := Finset.sum_subset (Finset.erase_subset _ _) (by
      intro J hJ hnot
      have hJI : J=I := by simpa using hnot
      subst J
      simp)

 

lemma translationMatrix_degree_bound {v s : ℕ} (u : Fin v → ℤ) (p : ℕ) (hp : 0<p)
    (hu : ∀ i, 0≤u i ∧ u i<p) (I J : PolynomialLineCoefficients.Grid v s)
    (hdeg : totalDegree I < totalDegree J) :
    |(translationMatrix u I J:ℝ)| ≤ ((2:ℝ)^s)^v * (p:ℝ)^(totalDegree J-totalDegree I) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hh := translationMatrix_bound u I J (p:ℝ) 1 hpR.le le_rfl (by
    intro i
    rw [one_mul,abs_of_nonneg (by exact_mod_cast (hu i).1)]
    exact_mod_cast (hu i).2.le)
  simp only [one_pow,mul_one] at hh
  apply (mul_le_mul_iff_left₀ (pow_pos hpR (totalDegree I))).mp
  calc
    _ ≤ ((2:ℝ)^s)^v * (p:ℝ)^totalDegree J := hh
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hdeg.le]

end RoughJointCoefficients

end
end
end

end OAI
