import OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergy
import OAI.NumberTheory.DirichletL.Reflection.MemberGeometryUniformDegree

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem canonical_member_geometry_uniform_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ), ∀ {Nlevel : Eis}, ∀
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (_hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (_hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (_hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (_hB : B≠0),
    ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d QK QP : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm I:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      QK/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      1≤QK → QK≤2*Z^M → 2≤QP → QP/2≤Z^z₀ →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
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
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(N-3*hhat)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2) := by
  let Lcap := 4*L+2
  have hLc : 0≤Lcap := by dsimp [Lcap];positivity
  obtain ⟨ε,ρ,κ,δ,π,hε,hρ,hκ,hδ,hδL,hηsmall,hδη,hπ,hbudget,hsmall⟩ :=
    canonical_reflection_parameters Lcap cstar η hLc hcstar hη hη1 hηc
  obtain ⟨degree,hu⟩ := original_member_geometry_uniform_uniform_degree
    ε hε lo hi hlo W hWs hW ρ hρ η hη κ δ (7*Lcap+1) Lcap hκ hδL hLc Lcap 1 hδ
  refine ⟨degree,?_⟩
  intro Nlevel γ _ a c₀ mode _ s hc₀ hNlevel hbase hac B hB
  obtain ⟨C,Z₁,hC,hZ₁,henergy⟩ := hu a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hwidth⟩ := width_error_threshold B hB 1 1 2 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  obtain ⟨Z₄,hZ₄,hlog⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max 2 (Ideal.absNorm B:ℝ)))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : max 2 (Ideal.absNorm B:ℝ)≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F R Q₀ hJ hI hF hR hpower hmask A
    Z N V M z₀ margin O₀ hhat d QK QP hZ hN hM hMc hVc hzc hhc
    hIn hFn hRn hO hOM hOn hKr hK1 hKc hP2 hPc hinv hmargin hVd hhd hd
  have hZ1 : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hZp : 0<Z := lt_trans zero_lt_one hZ1
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hz5.trans hZ)
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans (hz5.trans hZ)
  have hKp : 0<QK := lt_of_lt_of_le zero_lt_one hK1
  have hPp : 0<QP := by linarith
  have hPc' : QP≤2*Z^z₀ := by linarith
  obtain ⟨hFc,hKcap,hPcap,hXi⟩ := canonical_actual_arithmetic_caps L hL
    J I B F R Q₀ hJ hI hB hF hR hpower hmask A
    Z M V L z₀ N hhat QK QP hZ2 hBn hIn hFn hRn hMc hVc (le_refl _) hzc hN hhc hKc hPc'
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hXp : 0<Z^(N-3*hhat) := Real.rpow_pos_of_pos hZp _
  have hsc := hscale i G Z (Z^(N-3*hhat)) QK QP Lcap (hz2.trans hZ)
    hXp hKp.le hPp.le hFc hKcap hPcap hXi
  have hw := hwidth Z (hz3.trans hZ)
  have hza : 0≤Real.logb Z (QP/2) := Real.logb_nonneg hZ1 (by linarith)
  have hzac : Real.logb Z (QP/2)≤z₀ := by
    have he := Real.logb_le_logb_of_le hZ1 (by linarith : 0<QP/2) hPc
    rwa [Real.logb_rpow hZp (ne_of_gt hZ1)] at he
  have hzt : 0≤z₀ := hza.trans hzac
  have ht := canonical_reflected_target_positive (N+V) M (normWidth Z R) z₀ margin cstar O₀
    hinv hM (normWidth_nonneg Z hZ1 R hR) hzt hcstar hmargin hOM
  have hc := henergy i (σ:=σ) J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z (N+V) N V M z₀ margin cstar O₀ (Real.logb Z QK) (Real.logb Z (QP/2))
    (N-3*hhat) hhat d π 1 1 2 1 (Z^(N-3*hhat)) QK QP Lcap Lcap
    (hz1.trans hZ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hXp hKp hPp
    (by simpa using hIn) (by simpa using hOn) (dyadic_canonical_lower Z QK hZ1 hKp _ hKr)
    (by simpa using hFn) hw.1 hw.2 hinv rfl rfl hVd hhd rfl rfl
    (by rw [Real.logb_rpow hZp (ne_of_gt hZ1)]) hM hO hza hzac hcstar hmargin hd
    hηsmall hδη hπ hKcap (by linarith : QP/2≤Z^Lcap)
    (hlog Z (hz4.trans hZ)) hbudget hXi hKcap hPcap (by linarith : -1≤N+V-3*cstar/16-O₀/2)
    hFc hsc hFc hsmall
  exact hc
end
end SevenEighths.InverseReflectedPhase

end OAI
