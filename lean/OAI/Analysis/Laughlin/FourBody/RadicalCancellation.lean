import OAI.Analysis.Laughlin.FourBody.RadicalCoefficient

namespace OAI

namespace Laughlin.Spin

noncomputable def alphaRadical (t p j : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^((p : ℤ)-t) * ((t.factorial : ℝ)*((p+j-t).factorial : ℝ) /
    ((p.factorial : ℝ)*(j.factorial : ℝ))))
noncomputable def sourceCopyWeight (D r : ℕ) : ℝ :=
  1 / ((r.factorial : ℝ)*((D-r).factorial : ℝ))
noncomputable def sourceYFactor (D r s t p j q l : ℕ) : ℝ :=
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  (2 : ℝ)^((1 : ℤ)-2*T+p+q-t+((r+s)/2 : ℕ)) *
    ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ) / ((T-D).factorial : ℝ))

theorem source_Y_radical_cancellation (D r s t p j q l : ℕ)
    (hor : Odd r) (hos : Odd s) (he : t ≤ p+j) (hf : t ≤ q+l) :
    alphaRadical t p j * alphaRadical t q l *
      fourBodyRadical r D (p+j+(q+l-t)) p j (q+l-t) *
      fourBodyRadical s D (p+j+(q+l-t)) q l (p+j-t) =
    Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  let e : ℤ := 1-2*(T : ℤ)+p+q-t+((r+s)/2 : ℕ)
  have hT : p+j+k=T := rfl
  have hT' : q+l+i=T := by dsimp [i,k,T]; omega
  have hTr : (p : ℤ)+j+k=T := by exact_mod_cast hT
  have hTr' : (q : ℤ)+l+i=T := by exact_mod_cast hT'
  have heven : (((r+s)/2 : ℕ) : ℤ)*2=(r : ℤ)+s := by
    rcases hor with ⟨a,ha⟩; rcases hos with ⟨b,hb⟩
    omega
  have hex : ((p : ℤ)-t)+((q : ℤ)-t)+((1 : ℤ)-j-k-T+r)+((1 : ℤ)-l-i-T+s)=e*2 := by
    dsimp [e]; omega
  have hpowers : (2 : ℝ)^((p : ℤ)-t) * (2 : ℝ)^((q : ℤ)-t) *
      (2 : ℝ)^((1 : ℤ)-j-k-T+r) * (2 : ℝ)^((1 : ℤ)-l-i-T+s) = ((2 : ℝ)^e)^2 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),hex,zpow_mul]
    norm_num
  let F : ℝ := ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ))^2 /
    ((r.factorial : ℝ)*((D-r).factorial : ℝ)*(s.factorial : ℝ)*((D-s).factorial : ℝ)*((T-D).factorial : ℝ)^2)
  have hsq : (alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i)^2 =
      (Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l)^2 := by
    simp only [alphaRadical,fourBodyRadical,mul_pow]
    have hc0 : 0 ≤ sourceCopyWeight D r * sourceCopyWeight D s := by
      unfold sourceCopyWeight; positivity
    rw [Real.sq_sqrt hc0]
    repeat rw [Real.sq_sqrt (by positivity)]
    change (2^((p : ℤ)-t)*((t.factorial : ℝ)*i.factorial/(p.factorial*j.factorial))) *
      (2^((q : ℤ)-t)*((t.factorial : ℝ)*k.factorial/(q.factorial*l.factorial))) *
      (2^((1 : ℤ)-j-k-T+r)*((j.factorial : ℝ)*k.factorial*p.factorial /
        (r.factorial*(D-r).factorial*(T-D).factorial))) *
      (2^((1 : ℤ)-l-i-T+s)*((l.factorial : ℝ)*i.factorial*q.factorial /
        (s.factorial*(D-s).factorial*(T-D).factorial))) = _
    calc
      _ = (2^((p : ℤ)-t)*2^((q : ℤ)-t)*2^((1 : ℤ)-j-k-T+r)*2^((1 : ℤ)-l-i-T+s))*F := by
        dsimp [F]
        field_simp
      _ = ((2 : ℝ)^e)^2*F := by rw [hpowers]
      _ = _ := by
        dsimp [F,sourceYFactor,sourceCopyWeight]
        change ((2 : ℝ)^e)^2 * _ = (1/((r.factorial : ℝ)*(D-r).factorial) *
          (1/((s.factorial : ℝ)*(D-s).factorial))) *
          ((2 : ℝ)^e * ((i.factorial : ℝ)*k.factorial*t.factorial/(T-D).factorial))^2
        field_simp
  have hl : 0 ≤ alphaRadical t p j * alphaRadical t q l * fourBodyRadical r D T p j k *
      fourBodyRadical s D T q l i := by unfold alphaRadical fourBodyRadical; positivity
  have hr : 0 ≤ Real.sqrt (sourceCopyWeight D r * sourceCopyWeight D s) * sourceYFactor D r s t p j q l := by
    unfold sourceYFactor; positivity
  nlinarith only [hsq,hl,hr]

end Laughlin.Spin

end OAI
