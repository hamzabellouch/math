import OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry
import OAI.NumberTheory.DirichletL.Reflection.LowCaps
import OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
import OAI.NumberTheory.DirichletL.Reflection.SourceScaleCaps
import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem low_fixed_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (Q : Ideal Eis) (hQ : Q≠0) (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z d ell0 shift O₀ QK QP : ℝ),
      Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
      O₀=normWidth Z (rowPowerfulPart I) →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      QK/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      1≤QK → QK≤2*Ck*Z^(5/6-2*d) → 2≤QP → QP/2≤Z^ell0 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(1+ell0+shift)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+504*η-O₀/2) := by
  let ε := η/(200*(1+η))
  have hε : 0<ε := (low_reflection_parameters η hη).1
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := original_low_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac (η/8) (by positivity) η hη
    η (η/2) 57 8 hη (by positivity) (by norm_num) 8 2 (by positivity)
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hlogQ⟩ := constant_log_error (Ideal.absNorm Q:ℝ) η (actual_ideal_norm_pos Q hQ) hη
  obtain ⟨Z₄,hZ₄,hlogC⟩ := constant_log_error (2*Ck) η (by positivity) hη
  obtain ⟨Z₅,hZ₅,hlog16⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max Z₅ (max 2 (max Ck (Ideal.absNorm Q:ℝ)))))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : Z₅≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hzcap : max 2 (max Ck (Ideal.absNorm Q:ℝ))≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q₀ hJ hI hF hpower hmask A Z d ell0 shift O₀ QK QP
    hZ hd hd1 hell hellcap hshift hOeq hIn hKr hK1 hKcap hP2 hPcap
  have hz : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hzcap.trans hZ)
  have hCkZ : Ck≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  have hQZ : (Ideal.absNorm Q:ℝ)≤Z := (le_max_right _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
  obtain ⟨hIcap,hFcap,hK8,hP8,hX8⟩ := low_actual_scale_caps J I Q Q₀ hJ hI hQ hpower hmask A
    Z Ck d ell0 shift η QK QP hZ2 hCk hCkZ hQZ hd hell hellcap hshift hη1 hIn hKcap hPcap
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hXp : 0<Z^(1+ell0+shift) := Real.rpow_pos_of_pos hzpos _
  have hQK : 0<QK := by linarith
  have hQP : 0<QP := by linarith
  have hsc := hscale i G Z (Z^(1+ell0+shift)) QK QP 8 (hz2.trans hZ) hXp hQK.le hQP.le
    hFcap hK8 hP8 hX8
  norm_num only at hsc
  have hO : 0≤O₀ := hOeq ▸ normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero I)
  have hOp : 0<(Ideal.absNorm (rowPowerfulPart I):ℝ) := actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
  have hOn : Z^O₀=(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
    rw [hOeq]
    exact Real.rpow_logb hzpos (ne_of_gt hz) hOp
  have hO2 : O₀≤2 := by
    have hh := Real.logb_le_logb_of_le hz hOp ((original_powerful_norm_le I hI).trans hIcap)
    rw [←Real.rpow_natCast,Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    norm_num at hh
    exact hOeq.symm ▸ hh
  have hza : Real.logb Z (QP/2)≤ell0+η := by
    have hh := Real.logb_le_logb_of_le hz (by positivity : 0<QP/2) hPcap
    rw [Real.logb_rpow hzpos (ne_of_gt hz)] at hh
    linarith
  have hrowlower : Z^(Real.logb Z QK)/2≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    rw [Real.rpow_logb hzpos (ne_of_gt hz) hQK]
    exact hKr
  have hslot8 : QP/2≤Z^(8:ℝ) := by linarith
  have hbudget : ε*(8+8+2*(η/2+57+η))+η/2≤2*η := (low_reflection_parameters η hη).2
  have hh := he i (σ:=σ) J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ (Real.logb Z QK) (Real.logb Z (QP/2)) (1+ell0+shift) d ell0 shift (2*η)
    Ck 1 2 (Z^(1+ell0+shift)) QK QP 8 8
    (hz1.trans hZ) hCk (by norm_num) (by norm_num) hXp hQK hQP hIn
    (by simpa only [div_one,hOn] using le_refl (Ideal.absNorm (rowPowerfulPart I):ℝ)) hrowlower
    (by simpa only [mul_one] using hlogC Z (hz4.trans hZ))
    (by rw [hOeq];linarith) (hlogQ Z (hz3.trans hZ)) hd hd1 hellcap hO hza hshift rfl rfl rfl
    (by rw [Real.logb_rpow hzpos (ne_of_gt hz)]) (by positivity) (by linarith)
    hK8 hslot8 (hlog16 Z (hz5.trans hZ)) hbudget hX8 hK8 hP8 (by linarith)
    hFcap hsc hFcap
  dsimp only at hh ⊢
  intro rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := hh rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKn hPn hr haw
  apply (hD θ r aw hqk hqp hKn hPn hr haw).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
end
end SevenEighths.InverseReflectedPhase

end OAI
