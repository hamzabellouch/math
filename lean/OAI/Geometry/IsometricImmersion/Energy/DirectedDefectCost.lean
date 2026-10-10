import OAI.Geometry.IsometricImmersion.Energy.DirectedWeightJetCost

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem multiplierProduct_partial_abs_bound
    {A m : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hAv : |A p| ≤ M) (hmv : |m p| ≤ V)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V) (i : Fin 2) :
    |coordPartial i (fun q => A q*m q) p| ≤ 2*M*V := by
  rw [HessianCalculus.coordPartial_mul_at hA hm i]
  calc
    _ ≤ |coordPartial i A p*m p| + |A p*coordPartial i m p| := abs_add_le _ _
    _ ≤ M*V + M*V := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hAi i) hmv (abs_nonneg _) hM)
        ((mul_le_mul_of_nonneg_left (hmi i) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hAv hV))
    _ = _ := by ring

theorem multiplierCoefficients_abs_bound
    {A B C m n : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierT B m n p| ≤ (1+M)*V ∧
    |multiplierS A C m n p| ≤ (3*M)*V ∧
    |multiplierJ A B C m n p| ≤ (1+4*M)*V := by
  have hAm := multiplierProduct_partial_abs_bound hA hm hM hV hAv hmv hAi hmi
  have hAn := multiplierProduct_partial_abs_bound hA hn hM hV hAv hnv hAi hni
  have hprod {a b : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ V) : |a*b| ≤ M*V := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hM
  have hbn := hprod hBv hnv
  have hbm := hprod hBv hmv
  have hcm := hprod hCv hmv
  have hcn := hprod hCv hnv
  refine ⟨?_, ?_, ?_⟩
  · unfold multiplierT
    have hdiff : |coordPartial 1 m p - coordPartial 0 n p| ≤ 2*V :=
      (abs_sub _ _).trans (by linarith [hmi 1, hni 0])
    have hhalf : |(coordPartial 1 m p-coordPartial 0 n p)/2| ≤ V := by
      rw [abs_div]
      norm_num
      linarith
    exact (abs_add_le _ _).trans (by nlinarith only [hhalf, hbn])
  · unfold multiplierS
    have h1 : |-coordPartial 1 (fun q => A q*m q) p/2| ≤ M*V := by
      rw [abs_div, abs_neg]
      norm_num
      linarith [hAm 1]
    have h2 : |coordPartial 0 (fun q => A q*n q) p/2| ≤ M*V := by
      rw [abs_div]
      norm_num
      linarith [hAn 0]
    calc
      _ ≤ |-coordPartial 1 (fun q => A q*m q) p/2 +
          coordPartial 0 (fun q => A q*n q) p/2| + |C p*m p| := abs_add_le _ _
      _ ≤ (|-coordPartial 1 (fun q => A q*m q) p/2| +
          |coordPartial 0 (fun q => A q*n q) p/2|) + |C p*m p| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by nlinarith only [h1, h2, hcm]
  · unfold multiplierJ
    calc
      _ ≤ |-coordPartial 0 m p + B p*m p - coordPartial 1 (fun q => A q*n q) p| +
          |C p*n p| := abs_add_le _ _
      _ ≤ (|-coordPartial 0 m p+B p*m p| + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|-coordPartial 0 m p|+|B p*m p|) + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := by rw [abs_neg]; nlinarith only [hmi 0, hbm, hAn 1, hcn]

theorem multiplierQuadratic_abs_bound
    {A B C m n u : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierQuadratic A B C m n u p| ≤
      (2+8*M)*V*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
  obtain ⟨hT,hS,hJ⟩ := multiplierCoefficients_abs_bound hA hm hn hM hV hAv hBv hCv hAi hmv hnv hmi hni
  have hh := scalarQuadratic_abs_bound (x := coordPartial 0 u p) (y := coordPartial 1 u p) hT hJ hS
  have heq : multiplierQuadratic A B C m n u p =
      multiplierT B m n p*(coordPartial 0 u p)^2 +
      multiplierJ A B C m n p*(coordPartial 0 u p*coordPartial 1 u p) +
      multiplierS A C m n p*(coordPartial 1 u p)^2 := by unfold multiplierQuadratic; ring
  rw [heq]
  convert hh using 1
  ring

def directedQuadraticCostConstant (D M lambda S MI : ℝ) : ℝ :=
  (2+8*M)*directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)

theorem directedQuadratic_abs_le_seven
    {A B C I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) :
    |multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedQuadraticCostConstant D M lambda S MI * weightedGradient b u p := by
  obtain ⟨hmv,hnv,hmi,hni⟩ := directedMultiplier_firstJet_abs_le_seven
    hId hlambda hM heps heps1 ht hd hdD hs hIv hIi
  have hD : 0 ≤ D := hd.trans hdD
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  have hV : 0 ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    positivity
  have hh := multiplierQuadratic_abs_bound (u := u) hA
    (directedM_differentiableAt b lambda hId) (directedN_differentiableAt b lambda epsilon hId)
    hM hV hAv hBv hCv hAi hmv hnv hmi hni
  convert hh using 1
  unfold directedQuadraticCostConstant weightedGradient
  ring

theorem nonnegative_cutoff_defect_bound {chi a q : ℝ}
    (hchi : 0 ≤ chi ∧ chi ≤ 1) (ha : 0 ≤ a) : chi*max 0 (a-q) ≤ a+|q| := by
  have hmax : max 0 (a-q) ≤ a+|q| := by
    apply max_le
    · exact add_nonneg ha (abs_nonneg q)
    · linarith [neg_le_abs q]
  have hh := mul_le_mul hchi.2 hmax (le_max_left (0 : ℝ) (a-q)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using hh

def directedDefectCostConstant (D M lambda S MI c2 : ℝ) : ℝ :=
  c2*D*Real.exp (lambda*S+MI) + directedQuadraticCostConstant D M lambda S MI

theorem directedCoercivityDefect_le_seven
    {A B C chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M c2 : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      directedDefectCostConstant D M lambda S MI c2 * weightedGradient b u p := by
  have hQ := directedQuadratic_abs_le_seven (u := u) hA hId hlambda hM heps heps1 ht hd hdD
    hs hIv hIi hAv hBv hCv hAi
  have hW := directedWeight_le_seven hlambda hd hdD hs hIv
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ (coordPartial 0 u p)^2+(coordPartial 1 u p)^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hc2) hE
  have hbase := nonnegative_cutoff_defect_bound
    (q := multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    hchi (mul_nonneg (mul_nonneg hc2 hW0) hE)
  change directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ _ at hbase
  exact hbase.trans (by
    have hh := add_le_add hfirst hQ
    convert hh using 1
    unfold directedDefectCostConstant weightedGradient
    ring)

end SmoothLocal.Weighted

end

end OAI
