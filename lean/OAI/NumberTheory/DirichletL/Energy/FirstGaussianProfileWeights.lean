import OAI.NumberTheory.DirichletL.Energy.FirstGaussianCoefficients

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondChildPowerBudget CenteredMomentFirstChildProfileControl
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondWindowBudget
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def losses (epsilon delta theta B:ℝ):Fin 4→ℝ:=
  ![2*delta+epsilon,2*epsilon+2*delta+2*(5*B+1)*theta,0,0]

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

private lemma zero_control_le {a b:ℝ}(p:Profiles a b)(U:Finset (ℕ×ℕ))(h:(0,0)∈U):
    SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1)≤p.control U:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) h) (p.profile 1)) (apply_nonneg _ _) (sourceControl_nonneg _ _)

theorem actual_weights {a b:ℝ}(N:ℕ)(upper b1 b2 Amax loFloor:ℝ)
    (Cm Ce Cd Ct Cc cost epsilon delta theta B:ℝ)
    (Jprofile Jchild degree:ℕ)(Sp Tchild Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ))
    (hu:0≤upper)(hb1:0≤b1)(hb2:0≤b2)(_hAmax:0≤Amax)(hlo:0<loFloor)
    (hCm:0≤Cm)(hCe:0≤Ce)(hCd:0≤Cd)(hCt:0≤Ct)(hCc:0≤Cc)(hcost:0≤cost):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀Q:Ideal O,∀Kfix:ℝ,0≤Kfix→∃C:ℝ,0<C ∧
    ∀p:Profiles a b,∀Z t height A seed C0 C1:ℝ,
      0<Z→0≤height→0≤A→A≤Amax→1≤seed→0≤C0→0≤C1→
    let Ebase:=Cc*(C0+C1)*diagonalControl W*(p.control Tchild)^2*(1+height)^degree;
    ∀j:Fin 4,
      coefficients N upper b1 b2 A Sp p Jprofile Q Kfix t epsilon seed
        (fixedFactors Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed Jchild Sf W) j≤
      C*(C0+C1+1)*(p.control U)^2*(1+|t|+height)^J*Z^(losses epsilon delta theta B j)/seed:=by
  let U:=insert (0,0) (Sp∪Tchild)
  let J:=degree+(Jchild+Jchild)+2*Jprofile
  refine ⟨U,J,?_⟩
  intro Q Kfix hK
  let Hconst:ℝ:=(1+2*Real.pi)^2
  let D0:=Cm*cost*Cc*diagonalControl W*(profileMoment Jchild)^2*
    Hconst^(Jchild+Jchild)*(2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2)
  let D1:=Ce*loFloor^(-2/3:ℝ)*exceptionalConstant N upper Jprofile Q Kfix*Amax^4
  let D2:=Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖*4*(1+upper^N*b^2)^(1+epsilon)
  let D3:=Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hd:=diagonalControl_nonneg W
  have hmoment:=profileMoment_nonneg Jchild
  have hSf:0≤Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hExc:0≤exceptionalConstant N upper Jprofile Q Kfix:=by
    unfold exceptionalConstant
    positivity
  have hD0:0≤D0:=by dsimp [D0,Hconst];positivity
  have hD1:0≤D1:=by dsimp [D1];positivity
  have hD2:0≤D2:=by dsimp [D2];positivity
  have hD3:0≤D3:=mul_nonneg hCt hSf
  let C:=1+D0+D1+D2+D3
  have hC:0<C:=by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro p Z t height A seed C0 C1 hZ hheight hA hAA hseed hC0 hC1
  dsimp only
  let H:=1+|t|+height
  have hH:1≤H:=by dsimp [H];linarith [abs_nonneg t]
  have hH0:0≤H:=zero_le_one.trans hH
  have hseed0:0≤seed:=zero_le_one.trans hseed
  have hS:Sp⊆U:=by intro x hx;simp [U,hx]
  have hT:Tchild⊆U:=by intro x hx;simp [U,hx]
  have h00:(0,0)∈U:=by simp [U]
  have hp:=p.control_nonneg U
  have hpS:=p.control_nonneg Sp
  have hpT:=p.control_nonneg Tchild
  have hSpc: (p.control Sp)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpS hp).mpr (control_mono p hS)
  have hTpc: (p.control Tchild)^2≤(p.control U)^2:=
    (sq_le_sq₀ hpT hp).mpr (control_mono p hT)
  have h00c:(SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*
      SchwartzMap.seminorm ℝ 0 0 (p.profile 1))^2≤(p.control U)^2:=
    (sq_le_sq₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)) hp).mpr (zero_control_le p U h00)
  have hAp: A^2≤Amax^2:=pow_le_pow_left₀ hA hAA 2
  have hA4: A^4≤Amax^4:=pow_le_pow_left₀ hA hAA 4
  have hh:1+height≤H:=by dsimp [H];linarith [abs_nonneg t]
  have ht:1+‖t‖≤H:=by dsimp [H];linarith
  have henv0:0≤heightEnvelope t:=(heightEnvelope_pos t).le
  have henv:heightEnvelope t≤Hconst*H:=by
    have hx:1+|t|+2*Real.pi≤(1+2*Real.pi)*H:=by
      dsimp [H]
      nlinarith [Real.pi_pos,abs_nonneg t,
        mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg t)]
    have hy:=mul_le_mul_of_nonneg_right hx (show 0≤1+2*Real.pi by positivity)
    convert hy using 1 <;> dsimp [heightEnvelope,Hconst] ; ring
  have henvp:heightEnvelope t^(Jchild+Jchild)≤Hconst^(Jchild+Jchild)*H^(Jchild+Jchild):=by
    simpa only [mul_pow] using pow_le_pow_left₀ (heightEnvelope_pos t).le henv (Jchild+Jchild)
  have hheightp:(1+height)^degree≤H^degree:=pow_le_pow_left₀ (by positivity) hh degree
  have htp:(1+‖t‖)^(2*Jprofile)≤H^J:=
    (pow_le_pow_left₀ (by positivity) ht (2*Jprofile)).trans
      (pow_le_pow_right₀ hH (by dsimp [J];omega))
  have hjoin:H^degree*H^(Jchild+Jchild)≤H^J:=by
    rw [←pow_add]
    exact pow_le_pow_right₀ hH (by dsimp [J];omega)
  have hHone:1≤H^J:=one_le_pow₀ hH
  have hC01:0≤C0+C1:=add_nonneg hC0 hC1
  have hCplus:0≤C0+C1+1:=by positivity
  have hD (j:Fin 4): (![D0,D1,D2,D3] j)≤C:=by
    fin_cases j <;> simp only [Matrix.cons_val,Fin.reduceFinMk] <;> dsimp [C] <;> linarith
  have hbase (d:ℝ)(hd0:0≤d)(hdC:d≤C)(ell:ℝ):
      d*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed≤
      C*(C0+C1+1)*(p.control U)^2*H^J*Z^ell/seed:=by
    apply div_le_div_of_nonneg_right _ hseed0
    gcongr
  intro j
  fin_cases j
  · apply le_trans _ (hbase D0 hD0 (hD 0) (2*delta+epsilon))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Cm*Z^(2*delta+epsilon)*cost*
          (Cc*(C0+C1)*diagonalControl W*(p.control U)^2*H^degree)*
          (Hconst^(Jchild+Jchild)*H^(Jchild+Jchild))*profileMoment Jchild*profileMoment Jchild*
          (2*(b1*b2)*upper^N*Amax^2)*(upper^N*b1*b2):=by gcongr
      _=D0*(C0+C1)*(p.control U)^2*(H^degree*H^(Jchild+Jchild))*Z^(2*delta+epsilon):=by dsimp [D0];ring
      _≤D0*(C0+C1)*(p.control U)^2*H^J*Z^(2*delta+epsilon):=by gcongr
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD0)
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D1 hD1 (hD 1) (2*epsilon+2*delta+2*(5*B+1)*theta))
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ)*
          exceptionalConstant N upper Jprofile Q Kfix*(p.control U)^2*H^J*Amax^4:=by gcongr
      _=D1*(p.control U)^2*H^J*Z^(2*epsilon+2*delta+2*(5*B+1)*theta):=by dsimp [D1];ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD1 (le_add_of_nonneg_left hC01))
            (sq_nonneg (p.control U))) (pow_nonneg hH0 J))
        (Real.rpow_nonneg hZ.le _)
  · apply le_trans _ (hbase D2 hD2 (hD 2) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D2*(p.control U)^2:=by
        convert mul_le_mul_of_nonneg_left h00c hD2 using 1 ; dsimp only [D2] ; ring
      _≤D2*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D2*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD2 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone
  · apply le_trans _ (hbase D3 hD3 (hD 3) 0)
    dsimp only [CenteredMomentSecondChildPowerBudget.coefficients,fixedFactors,losses,Fin.isValue,Matrix.cons_val,Fin.reduceFinMk]
    rw [Real.rpow_zero,mul_one]
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hseed0
    calc
      _≤D3*(p.control U)^2:=mul_le_mul_of_nonneg_left h00c hD3
      _≤D3*(C0+C1+1)*(p.control U)^2*H^J:=by
        calc
          _≤D3*(C0+C1+1)*(p.control U)^2:=mul_le_mul_of_nonneg_right
            (le_mul_of_one_le_right hD3 (le_add_of_nonneg_left hC01)) (sq_nonneg _)
          _≤_:=le_mul_of_one_le_right (by positivity) hHone

end SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights

end

end OAI
