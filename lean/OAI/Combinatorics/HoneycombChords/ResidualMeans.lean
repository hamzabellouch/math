import OAI.Combinatorics.HoneycombChords.TaylorInterpolation

namespace OAI

/-! Point density and mean bounds for the two strip residual test functions.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv

lemma familyPointDensity_perm {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (p : Fin n → ℝ) (σ : Perm (Fin n)) :
    familyPointDensity w F G (p ∘ σ)=familyPointDensity w F G p := by
  have he (K : Fin n → ℝ → ℝ) :
      evaluationMatrix K (fun i=>(p (σ i))^2)=(evaluationMatrix K (fun i=>(p i)^2)).submatrix id σ := rfl
  simp only [familyPointDensity,Function.comp_apply,he,Matrix.det_permute']
  have hp : (∏ i,w (p (σ i)))=∏ i,w (p i) := Equiv.prod_comp σ (fun i=>w (p i))
  rw [hp]
  have hs : (((Perm.sign σ:ℤ):ℝ))*(((Perm.sign σ:ℤ):ℝ))=1 := by
    rw [←Int.cast_mul,←Units.val_mul,Int.units_mul_self];norm_num
  calc
    _=((((Perm.sign σ:ℤ):ℝ))*(((Perm.sign σ:ℤ):ℝ)))*
      ((∏ i,w (p i))*(evaluationMatrix F (fun i=>(p i)^2)).det*
        (evaluationMatrix G (fun i=>(p i)^2)).det) := by ring
    _=_ := by rw [hs,one_mul]

lemma familyPointDensity_eq_zero_of_not_injective {n : ℕ} (w : ℝ → ℝ)
    (F G : Fin n → ℝ → ℝ) (p : Fin n → ℝ) (hp : ¬Function.Injective p) :
    familyPointDensity w F G p=0 := by
  obtain ⟨i,j,he,hij⟩:=Function.not_injective_iff.mp hp
  have hz : (evaluationMatrix F (fun i=>(p i)^2)).det=0 := by
    apply Matrix.det_zero_of_column_eq hij
    intro k
    simp only [evaluationMatrix,he]
  rw [familyPointDensity,hz,mul_zero,zero_mul]

/-- Sorting is legitimate for the actual product of the two, possibly
nonsymmetric, evaluation determinants: both acquire the same sign. -/
lemma pointDensity_bound_of_sorted {n : ℕ} (w w₁ w₂ : ℝ → ℝ) (F G R : Fin n → ℝ → ℝ)
    (A B : ℝ)
    (hb : ∀ p : Fin n → ℝ,StrictMono p → (∀ i,0<p i) →
      familyPointDensity w R G p ≤ A*familyPointDensity w₁ F G p+B*familyPointDensity w₂ F G p) :
    ∀ p : Fin n → ℝ,(∀ i,0<p i) →
      familyPointDensity w R G p ≤ A*familyPointDensity w₁ F G p+B*familyPointDensity w₂ F G p := by
  intro p hp
  by_cases hpi : Function.Injective p
  · obtain ⟨d,σ,hd,he⟩:=sorted_injective_real hpi
    have hd0 i : 0<d i := by
      have h:=hp (σ.symm i)
      simpa only [he,Function.comp_apply,σ.apply_symm_apply] using h
    rw [he,familyPointDensity_perm,familyPointDensity_perm,familyPointDensity_perm]
    exact hb d hd hd0
  · rw [familyPointDensity_eq_zero_of_not_injective w R G p hpi,
      familyPointDensity_eq_zero_of_not_injective w₁ F G p hpi,
      familyPointDensity_eq_zero_of_not_injective w₂ F G p hpi]
    simp

lemma kernelOriginFunctional_eq_residual_det {n : ℕ} (b x : ℕ → ℝ) (u : ℝ)
    (H : ℝ → ℝ) :
    kernelOriginFunctional (n:=n) b u (fun i=>x i+u) (fun y=>1-H (y-u)/H (-u))=
      (evaluationMatrix (residualFamily (fun i : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i)) H (-u))
        (fun i=>x i)).det / (jetEvaluation b (fun i : Fin n=>x i)).det := by
  have he : translatedKernelMatrix (n:=n) b u (fun i=>x i+u)=jetEvaluation b (fun i : Fin n=>x i) := by
    ext i j
    dsimp [translatedKernelMatrix,jetEvaluation]
    congr 1 ; ring
  have hR : kernelComplementMatrix (n:=n) b u (fun i=>x i+u) (fun y=>1-H (y-u)/H (-u))=
      evaluationMatrix (residualFamily (fun i : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i)) H (-u))
        (fun i=>x i) := by
    ext i j
    dsimp [kernelComplementMatrix,evaluationMatrix,residualFamily]
    rw [show -u+(x j+u)=x j by ring,show x j+u-u=x j by ring]
    ring
  rw [kernelOriginFunctional,he,hR]

lemma normalized_residual_density {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a : ℝ) (p : Fin n → ℝ)
    (hd : (evaluationMatrix F (fun i=>(p i)^2)).det≠0) :
    familyPointDensity w (residualFamily F H a) G p=
      ((evaluationMatrix (residualFamily F H a) (fun i=>(p i)^2)).det /
      (evaluationMatrix F (fun i=>(p i)^2)).det)*familyPointDensity w F G p := by
  dsimp [familyPointDensity]
  field_simp

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset

noncomputable def fixedPoleProduct (x : ℕ  →  ℝ) (u c : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ range n,(x i+u)/(x i+c)
noncomputable def movingProduct (x : ℕ  →  ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ range n,(x i+2*T)/(x i+T)

lemma fixedPoleProduct_pos (x : ℕ  →  ℝ) {u c : ℝ} (hx : ∀ i,0 < x i)
    (hu : 0  ≤  u) (hc : 0 < c) (n : ℕ) : 0 < fixedPoleProduct x u c n :=
  prod_pos (fun i _ => div_pos (add_pos_of_pos_of_nonneg (hx i) hu) (add_pos (hx i) hc))
lemma fixedPoleProduct_le_one (x : ℕ  →  ℝ) {u c : ℝ} (hx : ∀ i,0 < x i)
    (hu : 0  ≤  u) (hc : 0 < c) (huc : u ≤ c) (n : ℕ) : fixedPoleProduct x u c n  ≤  1 := by
  apply prod_le_one₀
  · intro i _
    exact (div_pos (add_pos_of_pos_of_nonneg (hx i) hu) (add_pos (hx i) hc)).le
  · intro i _
    exact (div_le_one (add_pos (hx i) hc)).mpr (by linarith)

lemma movingProduct_ge_one (x : ℕ  →  ℝ) {T : ℝ} (hx : ∀ i,0 < x i) (hT : 0 < T) (n : ℕ) :
    1 ≤ movingProduct x T n := by
  apply one_le_prod₀
  intro i _
  exact (one_le_div (add_pos (hx i) hT)).mpr (by linarith)

lemma fixedPole_prefix_good {m n : ℕ} (hmn : m ≤ n) (x : ℕ  →  ℝ) {u c T : ℝ}
    (hx : ∀ i,0 < x i) (hu : 0 ≤ u) (hc : 0 < c) (hT : 0 < T)
    (hlarge : ∀ i,m ≤ i  →  i < n  →  T ≤ x i) :
    fixedPoleProduct x u c m  ≤  (1+c/T)^n*fixedPoleProduct x u c n := by
  have hK : 1 ≤ 1+c/T := by linarith [le_of_lt (div_pos hc hT)]
  have hfac (i) : 0 ≤ (x i+u)/(x i+c) := (div_pos (add_pos_of_pos_of_nonneg (hx i) hu) (add_pos (hx i) hc)).le
  have he : (∏ i ∈ range n,if i < m then (x i+u)/(x i+c) else 1)=fixedPoleProduct x u c m := by
    rw [←Nat.add_sub_of_le hmn,prod_range_add]
    have hz : (∏ i ∈ range (n-m),if m+i < m then (x (m+i)+u)/(x (m+i)+c) else 1)=1 := by
      apply prod_eq_one
      intro i _
      rw [ite_eq_right (by omega)]
    rw [hz,mul_one]
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_left (mem_range.mp hi)]
  rw [←he]
  calc
    _ ≤ ∏ i ∈ range n,(1+c/T)*((x i+u)/(x i+c)) := by
      apply prod_le_prod₀
      · intro i _
        split_ifs
        · exact hfac i
        · exact zero_le_one
      · intro i hi
        by_cases him : i < m
        · rw [ite_eq_left him]
          exact le_mul_of_one_le_left (hfac i) hK
        · rw [ite_eq_right him]
          have hXi:=hlarge i (by omega) (mem_range.mp hi)
          have hd : 0 < x i+c := add_pos (hx i) hc
          have hem : (1+c/T)*((x i+u)/(x i+c))=((1+c/T)*(x i+u))/(x i+c) := by ring
          rw [hem]
          apply (le_div_iff₀ hd).mpr
          have hTX : c ≤ c/T*x i := by
            have hmul:=mul_le_mul_of_nonneg_left hXi (div_pos hc hT).le
            simpa only [div_mul_cancel₀ _ hT.ne'] using hmul
          nlinarith [mul_nonneg (div_pos hc hT).le hu]
    _=(1+c/T)^n*fixedPoleProduct x u c n := by rw [prod_mul_distrib,prod_const,card_range];rfl

lemma movingProduct_prefix_bad {m n : ℕ} (hmn : m ≤ n) (x : ℕ  →  ℝ) {T : ℝ}
    (hx : ∀ i,0 < x i) (hT : 0 < T) (hsmall : ∀ i,i < m  →  x i ≤ T) :
    1  ≤  (2/3:ℝ)^m*movingProduct x T n := by
  have hprefix : (3/2:ℝ)^m  ≤  movingProduct x T m := by
    have he : (3/2:ℝ)^m=∏ i ∈ range m,(3/2:ℝ) := by rw [prod_const,card_range]
    rw [he]
    apply prod_le_prod₀
    · intro i _; norm_num
    · intro i hi
      apply (le_div_iff₀ (add_pos (hx i) hT)).mpr
      linarith [hsmall i (mem_range.mp hi)]
  have hmono : movingProduct x T m ≤ movingProduct x T n := by
    apply prod_le_prod_of_subset_of_one_le₀ (range_mono hmn)
    · intro i _
      exact (div_pos (by linarith [hx i]) (add_pos (hx i) hT)).le
    · intro i _ _
      exact (one_le_div (add_pos (hx i) hT)).mpr (by linarith)
  have h:=mul_le_mul_of_nonneg_left (hprefix.trans hmono) (by positivity : 0 ≤ (2/3:ℝ)^m)
  simpa only [←mul_pow,show (2/3:ℝ)*(3/2)=1 by norm_num,one_pow] using h

/-- A deterministic ordered-node estimate converting the first-N pole
product to the full characteristic product, with a moving-parameter error. -/
lemma fixedPole_prefix_bound {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (x : ℕ  →  ℝ) {u c T : ℝ}
    (hx : ∀ i,0 < x i) (hu : 0 ≤ u) (hc : 0 < c) (huc : u ≤ c) (hT : 0 < T)
    (hord : Monotone (fun i : Fin n => x i)) :
    fixedPoleProduct x u c m  ≤  (1+c/T)^n*fixedPoleProduct x u c n+
      (2/3:ℝ)^m*movingProduct x T n := by
  by_cases h : x (m-1) ≤ T
  · have hsmall (i : ℕ) (hi : i < m) : x i ≤ T :=
      (hord (show (⟨i,by omega⟩:Fin n) ≤ ⟨m-1,by omega⟩ from by simp;omega)).trans h
    have hb:=movingProduct_prefix_bad hmn x hx hT hsmall
    have hn : 0 ≤ (1+c/T)^n*fixedPoleProduct x u c n := by
      exact mul_nonneg (by positivity) (fixedPoleProduct_pos x hx hu hc n).le
    linarith [fixedPoleProduct_le_one x hx hu hc huc m]
  · have hlarge (i : ℕ) (hi : m ≤ i) (hin : i < n) : T ≤ x i := by
      have hi' := hord (show (⟨m-1,by omega⟩:Fin n) ≤ ⟨i,hin⟩ from by simp;omega)
      linarith
    have hb:=fixedPole_prefix_good hmn x hx hu hc hT hlarge
    have hn : 0 ≤ (2/3:ℝ)^m*movingProduct x T n :=
      mul_nonneg (by positivity) (le_trans zero_le_one (movingProduct_ge_one x hx hT n))
    linarith

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

noncomputable def stripJetFamily (N : ℕ) (t : ℝ) : Fin (2*N+1) → ℝ → ℝ :=
  fun i=>cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0 (interiorKnotLabels N t i)
noncomputable def nodeExtension {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun i=>if hi : i<n then x ⟨i,hi⟩ else 1
lemma nodeExtension_fin {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : nodeExtension x i=x i := by
  simp [nodeExtension]
lemma nodeExtension_pos {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i,0<x i) (i : ℕ) : 0<nodeExtension x i := by
  unfold nodeExtension
  split_ifs
  · exact hx _
  · norm_num
lemma nodeExtension_prod {n : ℕ} (x : Fin n → ℝ) (F : ℝ → ℝ) :
    (∏ i ∈ range n,F (nodeExtension x i))=∏ i,F (x i) := by
  rw [←Fin.prod_univ_eq_prod_range]
  simp only [nodeExtension_fin]

noncomputable def physicalFixedWeight (u p : ℝ) : ℝ := (p^2+u)/(p^2+physicalPole 0)
noncomputable def physicalMovingWeight (T p : ℝ) : ℝ := (p^2+2*T)/(p^2+T)

lemma physical_pole_product (x : ℕ → ℝ) (u : ℝ) (n : ℕ) :
    poleProduct (fun i=>x i+u) (shiftedPole u 0) n=fixedPoleProduct x u (physicalPole 0) n := by
  unfold poleProduct fixedPoleProduct shiftedPole
  apply prod_congr rfl
  intro i _
  congr 1 ; ring

lemma stripJet_positiveEvaluation (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    PositiveEvaluation (stripJetFamily N t) :=
  jet_positiveEvaluation _ (fun _ _ h=>interiorKnot_monotone N ht htL h)
    (fun i=>interiorKnot_nonneg N i t)


lemma stripJet_residual_density_bound {N : ℕ} (hN : 1 ≤ N) {u T s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) (H : ℝ → ℝ)
    (hb : ∀ x : ℕ → ℝ,(∀ i,0<x i) → StrictMono (fun i : Fin (2*N+1)=>x i) →
      kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N s) u (fun i=>x i+u)
        (fun y=>1-H (y-u)/H (-u)) ≤ 2*poleProduct (fun i=>x i+u) (shiftedPole u 0) N) :
    ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      familyPointDensity stripDensity (residualFamily (stripJetFamily N s) H (-u)) (stripJetFamily N t) p ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*
        familyPointDensity (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p+
      (2*(2/3:ℝ)^N)*
        familyPointDensity (fun p=>physicalMovingWeight T p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p := by
  apply pointDensity_bound_of_sorted
  intro p hp hp0
  let x : ℕ → ℝ:=nodeExtension (fun i=>(p i)^2)
  have hx (i) : 0<x i := nodeExtension_pos (fun i=>sq_pos_of_pos (hp0 i)) i
  have hxo : StrictMono (fun i : Fin (2*N+1)=>x i) := by
    intro i j hij
    simp only [x,nodeExtension_fin]
    exact (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij)
  have hK:=hb x hx hxo
  rw [physical_pole_product,kernelOriginFunctional_eq_residual_det] at hK
  have hP:=fixedPole_prefix_bound hN (by omega : N ≤ 2*N+1) x hx hu (physicalPole_pos 0)
    (hu4.trans (by norm_num [physicalPole])) hT hxo.monotone
  have hR : (evaluationMatrix (residualFamily (stripJetFamily N s) H (-u)) (fun i=>(p i)^2)).det /
        (evaluationMatrix (stripJetFamily N s) (fun i=>(p i)^2)).det ≤
      2*(1+physicalPole 0/T)^(2*N+1)*fixedPoleProduct x u (physicalPole 0) (2*N+1)+
        2*(2/3:ℝ)^N*movingProduct x T (2*N+1) := by
    have he : (fun i : Fin (2*N+1)=>x i)=(fun i=>(p i)^2) := by ext i;simp [x,nodeExtension_fin]
    rw [he] at hK
    change _ ≤ _ at hK
    change _ ≤ _
    calc
      _ ≤ 2*fixedPoleProduct x u (physicalPole 0) N := hK
      _ ≤ 2*((1+physicalPole 0/T)^(2*N+1)*fixedPoleProduct x u (physicalPole 0) (2*N+1)+
          (2/3:ℝ)^N*movingProduct x T (2*N+1)) := by linarith
      _=_ := by ring
  have hp2 : StrictMono (fun i=>(p i)^2) := by
    intro i j hij
    exact (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij)
  have hd:=(stripJet_positiveEvaluation N hs hsL) _ hp2 (fun i=>sq_pos_of_pos (hp0 i))
  have hbase : 0 ≤ familyPointDensity stripDensity (stripJetFamily N s) (stripJetFamily N t) p :=
    (familyPointDensity_pos _ _ _ _ (stripJet_positiveEvaluation N hs hsL)
      (stripJet_positiveEvaluation N ht htL) hp0 (fun _ h=>stripDensity_pos h) hp.injective).le
  rw [normalized_residual_density _ _ _ _ _ _ hd.ne']
  have he₁ : fixedPoleProduct x u (physicalPole 0) (2*N+1)=∏ i,physicalFixedWeight u (p i) := by
    unfold fixedPoleProduct
    exact nodeExtension_prod (fun i=>(p i)^2) (fun z=>(z+u)/(z+physicalPole 0))
  have he₂ : movingProduct x T (2*N+1)=∏ i,physicalMovingWeight T (p i) := by
    unfold movingProduct
    exact nodeExtension_prod (fun i=>(p i)^2) (fun z=>(z+2*T)/(z+T))
  have h:=mul_le_mul_of_nonneg_right hR hbase
  rw [he₁,he₂] at h
  rw [familyPointDensity_tilt,familyPointDensity_tilt]
  nlinarith only [h]

lemma hZero_point_density_upper {N : ℕ} (hN : 1 ≤ N) {u T s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) :
    ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      familyPointDensity stripDensity (residualFamily (stripJetFamily N s) (fun x=>(hZero x).re) (-u)) (stripJetFamily N t) p ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*
        familyPointDensity (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p+
      (2*(2/3:ℝ)^N)*
        familyPointDensity (fun p=>physicalMovingWeight T p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p := by
  apply stripJet_residual_density_bound hN hu hu4 hT hs hsL ht htL
  intro x hx hxo
  exact (source_hZero_kernel_bounds hN hu hu4 hs hsL x hx hxo).2

lemma hOne_point_density_upper {N : ℕ} (hN : 1 ≤ N) {u T s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) :
    ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      familyPointDensity stripDensity (residualFamily (stripJetFamily N s) (fun x=>(hOne x).re) (-u)) (stripJetFamily N t) p ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*
        familyPointDensity (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p+
      (2*(2/3:ℝ)^N)*
        familyPointDensity (fun p=>physicalMovingWeight T p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p := by
  apply stripJet_residual_density_bound hN hu hu4 hT hs hsL ht htL
  intro x hx hxo
  exact (source_hOne_kernel_bounds hN hu hu4 hs hsL x hx hxo).2

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Filter

lemma stripJet_pair_integrable (N : ℕ) {s t : ℝ} (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>stripJetFamily N s i (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  apply strip_jet_pair_integrable (interiorKnot_nonneg N i _) (interiorKnot_nonneg N j _)
  · exact (interiorKnot_le N i hs hsL).trans (by nlinarith [sq_nonneg angle])
  · exact interiorKnot_le N j ht htL

lemma stripJet_characteristic_pair_integrable (N : ℕ) {s t z : ℝ} (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) (hz : 0<z) (y : ℝ) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>stripJetFamily N s i (p^2)*stripJetFamily N t j (p^2)*
      (characteristicRatio y z p*stripDensity p)) (Set.Ioi 0) := by
  have h:=pole_jet_pair_pencil_integrable (interiorKnot_nonneg N i s) (interiorKnot_nonneg N j t)
    ((interiorKnot_le N i hs hsL).trans (by nlinarith [sq_nonneg angle]))
    (interiorKnot_le N j ht htL) hz (nodalOrder (interiorKnotLabels N s) i)
    (nodalOrder (interiorKnotLabels N t) j) (-(y^2))
  apply h.congr
  filter_upwards with p
  rw [congrFun (pole_pencil_tilt_weight y z) p]
  rfl

lemma hZero_sq_real (p : ℝ) (hp : 0 ≤ p) :
    (hZero (p^2)).re=1/(2*Real.cosh (angle*p)-1) := by
  rw [hZero,D_sq hp]
  norm_cast
  simp only [one_div]

lemma hOne_sq_real (p : ℝ) (hp : 0 ≤ p) :
    (hOne (p^2)).re=Real.cosh ((angle/2)*p)/(2*Real.cosh (angle*p)-1) := by
  rw [hOne,D_sq hp,C_sq _ hp]
  norm_cast

lemma hZero_sq_unit {p : ℝ} (hp : 0 ≤ p) : 0 ≤ (hZero (p^2)).re ∧ (hZero (p^2)).re ≤ 1 := by
  rw [hZero_sq_real p hp]
  have hd : 1 ≤ 2*Real.cosh (angle*p)-1 := by linarith [Real.one_le_cosh (angle*p)]
  constructor
  · positivity
  · exact (div_le_one (by linarith)).mpr hd

lemma hOne_sq_unit {p : ℝ} (hp : 0 ≤ p) : 0 ≤ (hOne (p^2)).re ∧ (hOne (p^2)).re ≤ 1 := by
  rw [hOne_sq_real p hp]
  have hd : 1 ≤ 2*Real.cosh (angle*p)-1 := by linarith [Real.one_le_cosh (angle*p)]
  have hc : Real.cosh ((angle/2)*p) ≤ Real.cosh (angle*p) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (mul_nonneg (by linarith [strip_angle_pos]) hp),
      abs_of_nonneg (mul_nonneg strip_angle_pos.le hp)]
    nlinarith [strip_angle_pos]
  constructor
  · positivity
  · apply (div_le_one (by linarith)).mpr
    linarith [Real.one_le_cosh (angle*p)]

lemma bounded_target_stripJet_integrable (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle)
    (H : ℝ → ℝ) (hHm : AEStronglyMeasurable (fun p=>H (p^2)) (volume.restrict (Set.Ioi 0)))
    (hH : ∀ p : ℝ,0<p → 0 ≤ H (p^2) ∧ H (p^2) ≤ 1) (j : Fin (2*N+1)) :
    IntegrableOn (fun p=>H (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  have hi:=strip_jet_pair_integrable (b:=0) (by rfl) (interiorKnot_nonneg N j t)
    (by positivity) (interiorKnot_le N j ht htL) 0 (nodalOrder (interiorKnotLabels N t) j)
  simp only [cosineKernelJet_at_zero,pow_zero,mul_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_mul] at hi
  have hfm : Continuous (fun p : ℝ=>stripJetFamily N t j (p^2)) :=
    (cosineKernelJet_contDiff_right _ 0 _ 0).continuous.comp (by fun_prop)
  apply hi.mono'
  · exact (hHm.mul hfm.aestronglyMeasurable).mul
      (show Measurable stripDensity by unfold stripDensity;fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hH0:=(hH p hp).1
    have hf0 : 0 ≤ stripJetFamily N t j (p^2) := cosineKernelJet_nonneg
      (interiorKnot_nonneg N j t) (sq_nonneg p) _ _
    have hw0 := (stripDensity_pos hp).le
    rw [Real.norm_of_nonneg (by positivity)]
    change H (p^2)*stripJetFamily N t j (p^2)*stripDensity p ≤ stripJetFamily N t j (p^2)*stripDensity p
    nlinarith [mul_nonneg (sub_nonneg.mpr (hH p hp).2) (mul_nonneg hf0 hw0)]

lemma hZero_stripJet_integrable (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) (j : Fin (2*N+1)) :
    IntegrableOn (fun p=>(hZero (p^2)).re*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  refine bounded_target_stripJet_integrable N ht htL (fun x=>(hZero x).re) ?_ ?_ j
  · apply (show Measurable (fun p : ℝ=>1/(2*Real.cosh (angle*p)-1)) by fun_prop).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact (hZero_sq_real p hp.le).symm
  · intro p hp
    exact hZero_sq_unit hp.le

lemma hOne_stripJet_integrable (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) (j : Fin (2*N+1)) :
    IntegrableOn (fun p=>(hOne (p^2)).re*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
  refine bounded_target_stripJet_integrable N ht htL (fun x=>(hOne x).re) ?_ ?_ j
  · apply (show Measurable (fun p : ℝ=>Real.cosh ((angle/2)*p)/(2*Real.cosh (angle*p)-1)) by fun_prop).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact (hOne_sq_real p hp.le).symm
  · intro p hp
    exact hOne_sq_unit hp.le

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter

lemma physicalFixedWeight_characteristic {u : ℝ} (hu : 0 ≤ u) :
    physicalFixedWeight u=characteristicRatio (Real.sqrt u) (8/3) := by
  funext p
  simp only [physicalFixedWeight,characteristicRatio,Real.sq_sqrt hu,physicalPole]
  norm_num

lemma physicalMovingWeight_characteristic {T : ℝ} (hT : 0 ≤ T) :
    physicalMovingWeight T=characteristicRatio (Real.sqrt (2*T)) (Real.sqrt T) := by
  funext p
  simp only [physicalMovingWeight,characteristicRatio,Real.sq_sqrt hT,
    Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hT)]

lemma stripJet_gram_det_pos (N : ℕ) {s t : ℝ} (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) :
    0<(familyGram stripDensity (stripJetFamily N s) (stripJetFamily N t)).det := by
  exact familyGram_det_pos _ _ _ (stripJet_positiveEvaluation N hs hsL)
    (stripJet_positiveEvaluation N ht htL) (fun _ hp=>stripDensity_pos hp)
    (stripJet_pair_integrable N hs hsL ht htL)

noncomputable def jetFixedMean (N : ℕ) (s t u : ℝ) : ℝ :=
  (familyGram (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t)).det /
    (familyGram stripDensity (stripJetFamily N s) (stripJetFamily N t)).det
noncomputable def jetMovingMean (N : ℕ) (s t T : ℝ) : ℝ :=
  (familyGram (fun p=>physicalMovingWeight T p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t)).det /
    (familyGram stripDensity (stripJetFamily N s) (stripJetFamily N t)).det

lemma stripJet_residual_mean_upper {N : ℕ} {u T s t : ℝ}
    (hu : 0 ≤ u) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) (H : ℝ → ℝ)
    (hHi : ∀ j,IntegrableOn (fun p=>H (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0))
    (hb : ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      familyPointDensity stripDensity (residualFamily (stripJetFamily N s) H (-u)) (stripJetFamily N t) p ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*
        familyPointDensity (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p+
      (2*(2/3:ℝ)^N)*
        familyPointDensity (fun p=>physicalMovingWeight T p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p) :
    meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) H (-u) ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*jetFixedMean N s t u+
        (2*(2/3:ℝ)^N)*jetMovingMean N s t T := by
  apply meanResidualRatio_bound
  · exact stripJet_pair_integrable N hs hsL ht htL
  · rw [physicalFixedWeight_characteristic hu]
    exact stripJet_characteristic_pair_integrable N hs hsL ht htL (by norm_num) _
  · rw [physicalMovingWeight_characteristic hT.le]
    exact stripJet_characteristic_pair_integrable N hs hsL ht htL (Real.sqrt_pos.mpr hT) _
  · exact hHi
  · exact stripJet_gram_det_pos N hs hsL ht htL
  · exact hb

lemma hZero_mean_upper {N : ℕ} (hN : 1 ≤ N) {u T s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) :
    meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-u) ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*jetFixedMean N s t u+
        (2*(2/3:ℝ)^N)*jetMovingMean N s t T :=
  stripJet_residual_mean_upper hu hT hs hsL ht htL _ (hZero_stripJet_integrable N ht htL)
    (hZero_point_density_upper hN hu hu4 hT hs hsL ht htL)

lemma hOne_mean_upper {N : ℕ} (hN : 1 ≤ N) {u T s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hT : 0<T) (hs : 0<s) (hsL : s<angle)
    (ht : 0<t) (htL : t<angle) :
    meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-u) ≤
      (2*(1+physicalPole 0/T)^(2*N+1))*jetFixedMean N s t u+
        (2*(2/3:ℝ)^N)*jetMovingMean N s t T :=
  stripJet_residual_mean_upper hu hT hs hsL ht htL _ (hOne_stripJet_integrable N ht htL)
    (hOne_point_density_upper hN hu hu4 hT hs hsL ht htL)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Equiv

lemma pointDensity_lower_of_sorted {n : ℕ} (w w₁ : ℝ → ℝ) (F G R : Fin n → ℝ → ℝ)
    (A : ℝ)
    (hb : ∀ p : Fin n → ℝ,StrictMono p → (∀ i,0<p i) →
      A*familyPointDensity w₁ F G p ≤ familyPointDensity w R G p) :
    ∀ p : Fin n → ℝ,(∀ i,0<p i) →
      A*familyPointDensity w₁ F G p ≤ familyPointDensity w R G p := by
  intro p hp
  by_cases hpi : Function.Injective p
  · obtain ⟨d,σ,hd,he⟩:=sorted_injective_real hpi
    have hd0 i : 0<d i := by
      have h:=hp (σ.symm i)
      simpa only [he,Function.comp_apply,σ.apply_symm_apply] using h
    rw [he,familyPointDensity_perm,familyPointDensity_perm]
    exact hb d hd hd0
  · rw [familyPointDensity_eq_zero_of_not_injective w R G p hpi,
      familyPointDensity_eq_zero_of_not_injective w₁ F G p hpi]
    simp

lemma meanResidualRatio_lower {n : ℕ} (w w₁ : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (H : ℝ → ℝ) (a A : ℝ)
    (hi : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hi₁ : ∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w₁ p) (Set.Ioi 0))
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hd : 0<(familyGram w F G).det)
    (hb : ∀ p : Fin n → ℝ,(∀ i,0<p i) →
      A*familyPointDensity w₁ F G p ≤ familyPointDensity w (residualFamily F H a) G p) :
    A*((familyGram w₁ F G).det/(familyGram w F G).det) ≤ meanResidualRatio w F G H a := by
  let μ:=Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hR:=family_gram_andreief w (residualFamily F H a) G (residualFamily_pair_integrable w F G H a hi hH)
  have h₁:=family_gram_andreief w₁ F G hi₁
  have hI:=integral_mono_ae (h₁.1.const_mul A) hR.1 (hae.mono hb)
  rw [integral_const_mul,hR.2,h₁.2] at hI
  have hc : (0:ℝ)<Fintype.card (Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  have hI' : A*(familyGram w₁ F G).det ≤ (familyGram w (residualFamily F H a) G).det := by nlinarith
  simpa only [meanResidualRatio,mul_div_assoc] using (div_le_div_of_nonneg_right hI' hd.le)

lemma stripJet_residual_density_lower {N : ℕ} {u s t : ℝ}
    (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (H : ℝ → ℝ) (A : ℝ)
    (hb : ∀ x : ℕ → ℝ,(∀ i,0<x i) → StrictMono (fun i : Fin (2*N+1)=>x i) →
      A*poleProduct (fun i=>x i+u) (shiftedPole u 0) (2*N+1) ≤
      kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N s) u (fun i=>x i+u)
        (fun y=>1-H (y-u)/H (-u))) :
    ∀ p : Fin (2*N+1) → ℝ,(∀ i,0<p i) →
      A*familyPointDensity (fun p=>physicalFixedWeight u p*stripDensity p) (stripJetFamily N s) (stripJetFamily N t) p ≤
        familyPointDensity stripDensity (residualFamily (stripJetFamily N s) H (-u)) (stripJetFamily N t) p := by
  apply pointDensity_lower_of_sorted
  intro p hp hp0
  let x : ℕ → ℝ:=nodeExtension (fun i=>(p i)^2)
  have hx (i) : 0<x i := nodeExtension_pos (fun i=>sq_pos_of_pos (hp0 i)) i
  have hp2 : StrictMono (fun i=>(p i)^2) := by
    intro i j hij
    exact (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij)
  have hxo : StrictMono (fun i : Fin (2*N+1)=>x i) := by simpa only [x,nodeExtension_fin] using hp2
  have hd:=(stripJet_positiveEvaluation N hs hsL) _ hp2 (fun i=>sq_pos_of_pos (hp0 i))
  have hbase : 0 ≤ familyPointDensity stripDensity (stripJetFamily N s) (stripJetFamily N t) p :=
    (familyPointDensity_pos _ _ _ _ (stripJet_positiveEvaluation N hs hsL)
      (stripJet_positiveEvaluation N ht htL) hp0 (fun _ h=>stripDensity_pos h) hp.injective).le
  have hR:=hb x hx hxo
  rw [kernelOriginFunctional_eq_residual_det,physical_pole_product] at hR
  simp only [x,nodeExtension_fin] at hR
  have he : fixedPoleProduct x u (physicalPole 0) (2*N+1)=∏ i,physicalFixedWeight u (p i) := by
    unfold fixedPoleProduct
    exact nodeExtension_prod (fun i=>(p i)^2) (fun z=>(z+u)/(z+physicalPole 0))
  rw [he] at hR
  have h:=mul_le_mul_of_nonneg_right hR hbase
  rw [normalized_residual_density _ _ _ _ _ _ hd.ne',familyPointDensity_tilt]
  have heval : jetEvaluation (interiorKnotLabels N s) (fun i : Fin (2*N+1)=>(p i)^2)=
      evaluationMatrix (stripJetFamily N s) (fun i=>(p i)^2) := rfl
  rw [heval] at h
  change (A*(∏ i,physicalFixedWeight u (p i)))*familyPointDensity stripDensity (stripJetFamily N s) (stripJetFamily N t) p ≤ _ at h
  rw [mul_assoc] at h
  exact h

lemma stripJet_residual_mean_lower {N : ℕ} {u s t : ℝ}
    (hu : 0 ≤ u) (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) (H : ℝ → ℝ) (A : ℝ)
    (hHi : ∀ j,IntegrableOn (fun p=>H (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0))
    (hb : ∀ x : ℕ → ℝ,(∀ i,0<x i) → StrictMono (fun i : Fin (2*N+1)=>x i) →
      A*poleProduct (fun i=>x i+u) (shiftedPole u 0) (2*N+1) ≤
      kernelOriginFunctional (n:=2*N+1) (interiorKnotLabels N s) u (fun i=>x i+u)
        (fun y=>1-H (y-u)/H (-u))) :
    A*jetFixedMean N s t u ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) H (-u) := by
  apply meanResidualRatio_lower
  · exact stripJet_pair_integrable N hs hsL ht htL
  · rw [physicalFixedWeight_characteristic hu]
    exact stripJet_characteristic_pair_integrable N hs hsL ht htL (by norm_num) _
  · exact hHi
  · exact stripJet_gram_det_pos N hs hsL ht htL
  · exact stripJet_residual_density_lower hs hsL ht htL H A hb

lemma hZero_mean_lower {N : ℕ} (hN : 1 ≤ N) {u s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) :
    jetFixedMean N s t u ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hZero x).re) (-u) := by
  simpa only [one_mul] using stripJet_residual_mean_lower hu hs hsL ht htL (fun x=>(hZero x).re) 1
    (hZero_stripJet_integrable N ht htL) (by intro x hx hxo; simpa only [one_mul] using (source_hZero_kernel_bounds hN hu hu4 hs hsL x hx hxo).1)

lemma hOne_mean_lower {N : ℕ} (hN : 1 ≤ N) {u s t : ℝ}
    (hu : 0 ≤ u) (hu4 : u ≤ 4) (hs : 0<s) (hsL : s<angle) (ht : 0<t) (htL : t<angle) :
    (1/2:ℝ)*jetFixedMean N s t u ≤ meanResidualRatio stripDensity (stripJetFamily N s) (stripJetFamily N t) (fun x=>(hOne x).re) (-u) :=
  stripJet_residual_mean_lower hu hs hsL ht htL _ _ (hOne_stripJet_integrable N ht htL)
    (fun x hx hxo=>(source_hOne_kernel_bounds hN hu hu4 hs hsL x hx hxo).1)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
