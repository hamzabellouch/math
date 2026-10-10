import OAI.Geometry.Convex.GeneralMahler.Budget.Extract

namespace OAI
/-! Pointwise Young estimate assembled before integrating; common
lemma for the two kernel estimates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Roots Seg
variable {m:ℕ} [NeZero m]

omit [NeZero m] in
lemma mats_s2 (a:ℝ) (f:Fin m→Fin m→ℝ) :
    a*mats (fun i=>∑ j,f i j) = mats (fun i=>∑ j,a*f i j) := by
  simp_rw [← Finset.mul_sum]; rw [mats_s]
omit [NeZero m] in
lemma mats_int (f:ℝ→Fin m→Fin m→ℝ) (hi:∀ i j,Integrable (fun x=> f x i j)) :
    Integrable (fun x=>mats (fun i=>∑ j,f x i j)) ∧
    (∫ x,mats (fun i=>∑ j,f x i j))=mats (fun i=>∑ j,∫ x,f x i j) := by
  unfold mats
  have hk (i:Fin m) : Integrable fun x:ℝ=>∑ j,f x i j :=
    integrable_finsetSum _ (fun j _=> hi i j)
  refine ⟨(integrable_finsetSum _ (fun i _=>hk i)).div_const _,?_⟩
  rw [integral_div,integral_finsetSum _ (fun i _=>hk i)]
  congr 1; apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _=>hi i j)]
lemma w_Young {a b c:ℝ} (hc:a^2≤b*c) (hb:0≤b) (he:0≤c) {klm:ℝ}
    (h:0<klm) (x y:ℝ) : -(x*y*a) ≤ klm*(x^2*b) + (4*klm)⁻¹*(y^2*c) := by
  by_cases hi:b=0
  · have hv : a=0 := by rw [hi] at hc; nlinarith
    rw [hi,hv]; simp; positivity
  have hk : 0<b := lt_of_le_of_ne hb (Ne.symm hi)
  field_simp
  have HH := sq_nonneg (2*klm*b*x+y*a)
  have hp := mul_le_mul_of_nonneg_left hc (sq_nonneg y)
  nlinarith

omit [NeZero m] in
lemma Frm.loc_s (u:Frm m) (t:ℝ) : u.loc (scalar m t)=scalar m t := by
  simp only [scalar,u.loc_smul,u.loc_one]
omit [NeZero m] in
lemma ctR_box {T:Mat m} (h:T∈specBox m tmin tmax) (u:Frm m) :
    u.loc T∈specBox m tmin tmax := by
  exact ⟨u.HL h.1,by simpa only [u.loc_s] using u.loc_le h.2.1,
    by simpa only [u.loc_s] using u.loc_le h.2.2⟩
omit [NeZero m] in
lemma ck_i {A:Rn m→Mat m} (h:regular A) (T:Mat m) :
    Integrable (fun x=>hsN (cmu (A x) T)) (normal m) := by
  let g := fun x=>cmu (A x) T
  have hg : regular g := ⟨(h.p.mul (PolyBound.const _)).sub ((PolyBound.const _).mul h.p),
    (h.meas.mul aestronglyMeasurable_const).sub (aestronglyMeasurable_const.mul h.meas)⟩
  have hs : regular (fun x=>star (g x)) := by
    refine ⟨hg.p.mono (fun x=>by rw [norm_star]),?_⟩
    exact continuous_star.comp_aestronglyMeasurable hg.meas
  have hl : regular (fun x=>g x*star (g x)) := ⟨hg.p.mul hs.p,hg.meas.mul hs.meas⟩
  have hi := hl.lin (trL)
  have he : (fun x=>hsN (g x)) = fun x=> trL (g x*star (g x)) := by funext x; rw [trL_apply];rfl
  change Integrable (fun x=> hsN (g x)) _
  rw [he]
  exact hi.ig
def Hcomm (A:Rn m→Mat m) (T:Mat m) := ∫ x,hsN (cmu (A x) T) ∂normal m

namespace ProjField
variable (q:ProjField m) (B:FieldMat m) (T:Mat m)

-- f,b profiles in k; R profile for diagonal gain; bAv f gives matrix subtracted pairing.
-- κ₀ scales both f and U choice exposed
lemma Klimit (ht:T∈specBox m tmin tmax)
    {f w R:Plane→ℝ} (hf:Bwt f) (hw:Bwt w) (hR:Bwt R)
    (hp:∀ v:Plane,0≤w v)
    (c:ℝ) (_hc:0≤c)
    (hmat:∀ (z:ℝ) (l:Fin m→ℝ) (t:Mat m), t∈specBox m tmin tmax →
      Matrix.diagonal (fun i=>R (z,l i)) ≤
        c • jprod t (diagonal (fun i=> bAv f (z,l i))))
    (U:ℝ→ℝ→ℝ→ℝ) (b₀:ℝ)
    (hU:∀ x y,Integrable (U x y) ∧ (∫ z,U x y z)=b₀*(x-y)^2)
    (hu:∀ x y z,z≠x→z≠y→0≤U x y z)
    (hK:∀ x y z,z≠x→z≠y→ (c*kz f x y z)^2≤
      ((|x-z| * w (z,x)+|y-z| * w (z,y))/2)*U x y z)
    {klm:ℝ} (h:0<klm) :
    q.BB B R - c*q.LLw B T f ≤ klm*q.BB B w + b₀/(4*klm)*Hcomm B.A T := by
  have he (x:Rn m) :
      (∫ z,q.bmZ B R z x)- c*(∫ z,q.lk B T f z x) ≤
      klm*(∫ z,q.bmZ B w z x)+ b₀/(4*klm)*hsN (cmu (B.A x) T) := by
    let u := B.Fr x
    let t := u.loc T
    let y := B.ev x
    let g := fun z:ℝ=> mats (fun i:Fin m=>∑ j:Fin m, (t j i)^2* U (y i) (y j) z)
    have hm (i j:Fin m) := hU (y i) (y j)
    have ha := mats_int (fun z i j=> (t j i)^2 * U (y i) (y j) z) (fun i j=>(hm i j).1.const_mul _)
    have hh : (∫ z,g z)=b₀*hsN (cmu (B.A x) T) := by
      unfold g
      rw [ha.2,cmu_eig (B.A x) T u (B.Fr_D x)]
      simp_rw [integral_const_mul]
      rw [← mats_s]
      congr 1; ext i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      rw [(hm _ _).2,symm_entry (u.HL ht.1)]
      change _ = b₀*((y i-y j)^2 * (t j i)^2)
      ring
    have ha' : Integrable g := ha.1
    let m₁ := fun z=>q.bmZ B R z x - c*q.lk B T f z x
    let m₂ := fun z=>klm*q.bmZ B w z x +(4*klm)⁻¹*g z
    have hi₁ := q.bmh B hR x; have hi₂ := q.lk_slice_i B T hf x
    have hi₃ := q.bmh B hw x
    have he : ∀ᵐ z:ℝ, m₁ z≤ m₂ z := by
      have he : ∀ᵐ z:ℝ,∀ i:Fin m,z≠y i :=
        ae_all_iff.2 fun i=>by rw [ae_iff]; simp
      filter_upwards [he] with z hz
      let b := q.BL B x z
      let V := Matrix.diagonal fun i=> bAv f (z,y i)
      have hs := trN_mul_mono (hmat z y t (ctR_box ht u)) b.Spar
      rw [trN_cyclic _ b.S,trN_cyclic _ b.S,traceDiag,mul_smul_comm,trN_smul] at hs
      let J := fun i j:Fin m=> b.E i j*t j i*kz f (y i) (y j) z
      let d := fun i j:Fin m=>(|y i-z| * w (z,y i)+ |y j-z| * w (z,y j))/2
      let k:=fun i=>∑ j,b.E i j^2*d i j
      have hJ (i j) : (-c)*J i j ≤ klm*(b.E i j^2*d i j)+(4*klm)⁻¹*(t j i^2*U (y i) (y j) z) := by
        have hh := hp (z,y i); have hhh := hp (z,y j)
        have ht := hK (y i) (y j) z (hz _) (hz _)
        change _ ≤ d i j*_ at ht
        apply le_trans _ (w_Young ht (by unfold d; positivity) (hu _ _ _ (hz _) (hz _)) h (b.E i j) (t j i))
        unfold J; apply le_of_eq; ring
      have hi :
          (-c)*mats (fun i=> ∑ j,J i j)≤ klm*mats k+(4*klm)⁻¹*g z := by
        unfold g k; rw [mats_s2,mats_s2,mats_s2,← mats_add]
        apply mats_le; intro i; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun j _=>hJ _ _
      have he : mats k≤ q.bmZ B w z x := by
        have ht:= b.tr_blk (fun i=> w (z,y i)) (fun i=> hp _)
        rw [q.bm_trace]
        change _ ≤ mats (fun i=>b.S i i*w (z,y i))
        apply le_trans _ ht
        unfold k d
        apply le_of_eq; congr 1; funext i
        apply Finset.sum_congr rfl; intro j _
        exact mul_comm ..
      unfold m₁ m₂
      rw [q.pairing_layer B T x z hf ht.1,q.bm_trace B x z R]
      change mats (fun i=> b.S i i*R (z,y i))-c*(trN (b.S*jprod t V)+mats (fun i=>∑ j,J i j))
        ≤ klm*q.bmZ B w z x+(4*klm)⁻¹*g z
      change mats _≤ c*trN (b.S*jprod t V) at hs
      linarith [mul_le_mul_of_nonneg_left he h.le]
    have hp := integral_mono_ae (show Integrable m₁ volume from hi₁.sub (hi₂.const_mul c))
      (show Integrable m₂ volume from (hi₃.const_mul _).add (ha'.const_mul _)) he
    unfold m₁ m₂ at hp
    rw [integral_sub hi₁ (hi₂.const_mul _),integral_add (hi₃.const_mul _) (ha'.const_mul _)] at hp
    simp_rw [integral_const_mul,hh] at hp
    rw [div_eq_mul_inv]; linarith
  unfold BB LLw Hcomm
  have hi := q.bmah B hR; have hh := q.Lbar_i B T hf
  have hg := q.bmah B hw
  rw [← integral_const_mul,← integral_const_mul,← integral_const_mul]
  have hx := ck_i B.reg T
  rw [← integral_sub hi (hh.const_mul _), ← integral_add (hg.const_mul _) (hx.const_mul _)]
  exact integral_mono (hi.sub (hh.const_mul _)) ((hg.const_mul _).add (hx.const_mul _)) he
end ProjField
end GeneralMahler

end

end OAI
