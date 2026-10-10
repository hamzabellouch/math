import OAI.NumberTheory.DirichletL.Moments.FirstSecondPaidLedger
import OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstPhysicalLedger
local notation "O"=>ActualEisensteinCubic.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0<H
  hX:0<X
  hCsec:1≤Csec
  hξ:0≤ξ
  hsec:Tsec≤Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤q
  hw:0≤w
  hwo:0≤wo
  hell:0≤ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

def removedWidth {Z:ℝ}(s:Branch Z):ℝ:=
  Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+s.w

def saving {Z:ℝ}(s:Branch Z):ℝ:=
  let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
  let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
  let p:=Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)
  let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
  let e:=Real.logb Z (s.E.absNorm:ℝ)
  let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
    Real.logb Z (dyadicScale s.n)
  firstSaving c D₀ s.w (s.q+R+e) s.wo (c+d-2*p-R)
    (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell

def loss {Z:ℝ}(s:Branch Z):ℝ:=3*s.σ+5*frequencyLoss Z s.Csec s.ξ/6

def rawCap (Z:ℝ)(X red:Fin 2→ℝ):ℝ:=
  min (Real.logb Z (X 0/red 0)) (Real.logb Z (X 1/red 1))

lemma actual_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤saving s:=by
  have hh:=actual_first_saving s.I s.J s.E s.hI s.hJ s.hE Z s.H s.X s.Tsec s.Csec
    s.ξ s.q s.w s.wo s.ell s.σ s.kind hZ s.hH s.hX s.hCsec s.hξ s.hsec
    s.n s.hn s.hq s.hw s.hwo s.hell s.hσ s.hkind s.hwσ
  simpa only [removedWidth,loss,saving,sub_add_eq_sub_sub] using hh

lemma raw_cap_lower (Z L d:ℝ)(hZ:1<Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^L≤X i)(hred:∀i,0<red i)(hupper:∀i,red i≤Z^d):
    L-d≤rawCap Z X red:=by
  have h (i:Fin 2):L-d≤Real.logb Z (X i/red i):=by
    have hz:0<Z:=zero_lt_one.trans hZ
    have hx:0<X i:=(Real.rpow_pos_of_pos hz L).trans_le (hX i)
    have hl:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz L) (hX i)
    have hr:=Real.logb_le_logb_of_le hZ (hred i) (hupper i)
    rw [Real.logb_rpow hz hZ.ne'] at hl hr
    rw [Real.logb_div hx.ne' (hred i).ne']
    linarith
  exact le_min (h 0) (h 1)

theorem actual_branch_stage (Z A M:ℝ)(hZ:1<Z)(s:Branch Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^(M/4)≤X i)(hred:∀i,0<red i)
    (hupper:∀i,red i≤Z^(removedWidth s)):
    A-5*M/6-saving s-2*max (rawCap Z X red) 0/3≤A-M+loss s:=by
  have hs:=actual_saving hZ s
  have hr:=raw_cap_lower Z (M/4) (removedWidth s) hZ X red hX hred hupper
  have hm:=le_max_left (rawCap Z X red) (0:ℝ)
  linarith

theorem actual_paired_stage (Z A M:ℝ)(hZ:1<Z)(s:Fin 2→Branch Z)
    (X red:Fin 2→Fin 2→ℝ)
    (hX:∀j i,Z^(M/4)≤X j i)(hred:∀j i,0<red j i)
    (hupper:∀j i,red j i≤Z^(removedWidth (s j))):
    A-5*M/6-(saving (s 0)+saving (s 1))/2-
      (max (rawCap Z (X 0) (red 0)) 0+max (rawCap Z (X 1) (red 1)) 0)/3≤
      max (A-M) 0+(loss (s 0)+loss (s 1))/2:=by
  have h₀:=actual_branch_stage Z A M hZ (s 0) (X 0) (red 0) (hX 0) (hred 0) (hupper 0)
  have h₁:=actual_branch_stage Z A M hZ (s 1) (X 1) (red 1) (hX 1) (hred 1) (hupper 1)
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

end SevenEighths.CenteredMomentFirstExceptionalPaidScales

end

end OAI
