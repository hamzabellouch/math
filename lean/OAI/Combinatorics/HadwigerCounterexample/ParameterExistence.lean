import OAI.Combinatorics.HadwigerCounterexample.AnalyticParameters

namespace OAI

/-! # Parameter Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

def birthG : ℕ := 10^9+1
structure Ribbon (b : PreparationParameters) : Prop where
  life : b.allows
  hd : b.D=4000*birthG
  mercury : b.L=bp 1000
  rain : (b.D:ℝ)+b.ζ ≤ (b.ζ-b.ζ/4)*b.e
  hk : b.k≤ b.d
  beam : b.spJoint+1 ≤ 0.49*b.k
  dul : 3*b.d+2*b.e+2≤b.u
  size : frameBills birthG b.pins+1000 ≤ b.B
  dust : 2*b.ζ ≤0.004∧2*b.ζ*(56*((birthG-1:ℕ):ℝ))≤0.004

theorem floor_supply (x : ℝ) (y : ℝ) (hy : 0<y) : ∃ k : ℕ,x≤ y*k := by
  obtain ⟨i,hi⟩ := ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (eventually_ge_atTop (x/y))).exists
  refine ⟨i,?_⟩
  rw [mul_comm]; exact (div_le_iff₀ hy).mp hi

set_option maxHeartbeats 1400000 in
theorem seed_ribbon : ∃ b : PreparationParameters, Ribbon b := by
  classical
  let x : ℝ := 56*((birthG-1:ℕ):ℝ)
  let ζ := 1/(1000*x)
  have hx : 1≤x := by norm_num [x,birthG]
  have hq : 0<ζ ∧ ζ≤1/1000 := by
    unfold ζ
    exact ⟨by positivity,(div_le_iff₀ (by positivity)).mpr (by linarith)⟩
  have hz : 0<ζ-ζ/4:=by linarith only [hq.1]
  let D:=4000*birthG
  obtain ⟨e,he⟩:=floor_supply ((D:ℝ)+ζ) _ hz
  obtain ⟨k,hk⟩:=floor_supply ((D:ℝ)+1+1) 0.49 (by norm_num)
  let d:= (2*e+2)*4*k
  let u:=10*(e+d+1)
  obtain ⟨r,hr⟩:=floor_supply ((D:ℝ)+e+2+u+ζ) _ hz
  let b : PreparationParameters:=⟨D,bp 1000,d,e,r,u,k,ζ,
      10*(frameBills birthG (3*e+r)+10000*birthG+1)⟩
  refine ⟨b,⟨⟨hq.1, hq.2.trans_lt (by norm_num), (bp_pos _).le, hr⟩, rfl,rfl,he,?_,hk,?_,?_,?_⟩⟩
  · change k ≤ d; unfold d; nlinarith
  · change 3*d+2*e+2 ≤ u; unfold u; omega
  · change frameBills birthG (3*e+r)+1000 ≤ 10*(_+10000*birthG+1)
    have hh : 3≤ birthG := by norm_num [birthG]
    omega
  change 2*ζ≤_ ∧ 2*ζ*x≤_
  refine ⟨by linarith only [hq.2],?_⟩
  have hg : ζ*x=1/1000 := by unfold ζ; field_simp
  linarith only [hg]

private def layout (g b j J r : ℕ) : Shape := ⟨g,b,j,J,r,1000*r⟩

private theorem lanesNeed (q b j J : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      let p:= layout birthG b j J r
      rankAll p q+2*(q+2*(3*blin q))≤p.h := by
  let p:=layout birthG b j J 0
  let x:= rankAll p q +2*(q+2*(3*blin q))
  filter_upwards [eventually_ge_atTop x] with r hr
  let p':=layout birthG b j J r
  dsimp only
  change rankAll p' q + _≤ 1000*r
  have hh : rankAll p' q=rankAll p q+30*r := by
    unfold rankAll rankInit
    change 2*(15*r+14*J*ncComp p)+dqBound p (q+14) q (rankRes q)=_
    change _= 2*(15*0+14*J*ncComp p)+dqBound p (q+14) q (rankRes q)+30*r
    ring
  rw [hh]; unfold x at hr
  omega

private theorem altitude_need (q b j J : ℕ) :
    ∀ᶠ r : ℕ in atTop,
      let p:= layout birthG b j J r
      2*screenRank p q+1 ≤ ((p.g-1)/2)*(p.g-16000)*p.r := by
  filter_upwards [eventually_ge_atTop (J*q+1)] with r hr
  unfold screenRank layout
  dsimp only
  norm_num only [birthG]
  norm_num [birthG] at *
  rw [Nat.mul_assoc 2 J]
  omega

private theorem labels_large (j B g : ℕ) (hg : 3≤g) :
    ∃ b:ℕ,(B:ℝ)<bp ((b:ℝ)-2*j) ∧ 3*B < Fintype.card (Label b) := by
  classical
  obtain ⟨b,hb⟩ := ((bp_poly_dom_nat (a:=1) zero_lt_one
    (100*g*(B+1:ℝ)*bp (2*j)) 0)).exists
  have he : 100*g*(B+1:ℝ)*bp (2*j)< bp (b:ℝ) := by simpa using hb
  have hb' : (B:ℝ)<bp ((b:ℝ)-2*j) := by
    rw [bp_sub,lt_div_iff₀ (bp_pos _)]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by
      have hh : 3≤(g:ℝ) := by exact_mod_cast hg
      nlinarith [(Nat.cast_nonneg B : 0≤(B:ℝ))]) (bp_pos _).le) he
  have hb'' : 3*B < Fintype.card (Label b) := by
    have hs : 1 ≤ bp (2*j) := by rw [←bp_zero]; exact bp_le (by positivity)
    have hh : Fintype.card (Label b)=2^b := by simp [Label,F]
    have heq : 3*(B:ℝ) < bp b := by
      have hh : 3≤(g:ℝ):=by exact_mod_cast hg
      refine lt_of_le_of_lt ?_ he
      have hz : 100*g*(B+1:ℝ) ≤ 100*g*(B+1:ℝ)*bp (2*j) := by
        exact le_mul_of_one_le_right (by positivity) hs
      nlinarith [(Nat.cast_nonneg B :0≤(B:ℝ))]
    rw [hh]; rw [bp_nat] at heq; exact_mod_cast heq
  exact ⟨b,hb',hb''⟩

set_option maxHeartbeats 240000 in
theorem exists_parameters : ∃ (p : Shape) (b : PreparationParameters) (M r : ℕ),AnalyticParameters p M b r ∧
    p.g=birthG ∧ b.D=4000*p.g ∧ b.L=bp 1000 := by
  classical
  obtain ⟨t,ht⟩:=seed_ribbon
  let K:=t.pins; let g:=birthG
  have hg : 3 ≤ g := by norm_num [g,birthG]
  have hx : Odd g := by
    unfold g birthG; use 500000000; norm_num
  let j:= 10*(K+1)*(Rorth K+20)
  have hj : (K+1)*qorth K≤j+1 := by unfold j qorth; nlinarith
  have hj' : 6*Rorth K+4≤j := by unfold j; nlinarith
  obtain ⟨b,hb',hb''⟩:=labels_large j t.B g hg
  let C:=profileA (layout g b j 0 0) K
  let r:=4*C+1
  let J:=100*(r+K^2+1)+1
  have hyJ : 1≤J ∧ r≤J := by unfold J; omega
  have hJ : bp (-((J-r:ℕ):ℝ))*bp r < glintRate K := by
    rw [←bp_add]; apply bp_lt
    have hh : K^2+4+r≤J-r := by unfold J; omega
    have hi : ((K^2:ℕ):ℝ)+4+(r:ℝ) ≤ ((J-r:ℕ):ℝ) := by exact_mod_cast hh
    linarith only [hi]
  have hU : 8*t.D<g*g:=by rw [ht.hd]; norm_num [g,birthG]
  have hD : 0<t.D:=by rw [ht.hd]; norm_num [birthG]
  obtain ⟨h0,hA⟩:= Filter.eventually_atTop.mp (PreparationParameters.stamp g t ht.life hD ht.rain ht.hk
    ht.beam ht.dul)
  obtain ⟨y,hc,he,hy,_hx⟩:= ((lanesNeed K b j J).and ((altitude_need t.e b j J).and
    ((eventually_ge_atTop (1:ℕ)).and (eventually_ge_atTop h0)))).exists
  let p:=layout g b j J y
  have hp : realizeAssum p K:= ⟨hx,hj',hc⟩
  have hY : 1≤p.j := show 1≤j by omega
  have he' := hA p.h (show h0≤1000*y by omega) p rfl rfl hx hg hY hy hb' hU
    ⟨16000,(by change 4*t.D ≤ g*16000; rw [ht.hd]; norm_num [g,birthG]),he⟩
  obtain ⟨M,hM,hM',hK⟩:= (he'.and ((eventually_ge_atTop (4:ℕ)).and
    (collision_scales p K))).exists
  have hF : 2*C<r := by unfold r; omega
  refine ⟨p,t,M,r, ⟨hM,hM',show 2*C<r from hF,hyJ.1,hyJ.2,hJ,hj,ht.size,hb'',?_⟩,rfl,
    ht.hd,ht.mercury⟩
  filter_upwards [hK,eventually_ge_atTop (2*y)] with n hn he
  refine ⟨hy,he,hp,by linarith only [ht.life.pos],ht.dust.1, ?_,hn.1,hn.2.1,hn.2.2⟩
  unfold kmax; push_cast
  exact ht.dust.2
end HadwigerCounterexample

end

end OAI
