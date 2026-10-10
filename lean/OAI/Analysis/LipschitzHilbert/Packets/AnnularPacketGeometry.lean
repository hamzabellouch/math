import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSymbolForm
import OAI.Analysis.LipschitzHilbert.Estimates.OrdinaryModelNumerics

namespace OAI

/-! Fixed numerical choices for the annular multiplier. The enlargement
and compact master radius depend only on its support and on the two
frequency-window widths. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

structure AnnularPacketGeometry (A B c C a M : ℝ) where
  H : ℝ
  R : ℝ
  hA : 0≤A
  hB : 0≤B
  hc : 0<c
  hC : 0<C
  ha : 0<a
  hM : 0<M
  hH : 1≤H
  hR : 0<R
  narrow : A≤a/4
  size : A+B+(M+A)/(H*c)≤R
  radius : max (H*C) H≤R
  quarter : (3*a/(4*(H*C)))/2≤1/4
  separation : (2*Real.pi*A)/(2*Real.pi*(H*c))<(3*a/(4*(H*C))/2)/4
  coverage : 6*max (2*((M+A)/(H*c)))
    ((2*Real.pi*A)/(2*Real.pi*(H*c))+3*a/(4*(H*C))/2)<1

namespace AnnularPacketGeometry
variable {A B c C a M : ℝ} (p : AnnularPacketGeometry A B c C a M)

def inner : ℝ := 3*a/(4*(p.H*C))
def outer : ℝ := (M+A)/(p.H*c)
theorem H_pos : 0<p.H := zero_lt_one.trans_le p.hH
theorem inner_pos : 0<p.inner := by unfold inner; positivity [p.H_pos,p.hC,p.ha]
theorem outer_pos : 0<p.outer := by unfold outer; positivity [p.H_pos,p.hc,p.hM,p.hA]

def numerics : PacketLatticeData.OrdinaryModelNumerics
    (2*Real.pi*A) (2*Real.pi*(p.H*c)) (p.inner/2) (2*p.outer) :=
  Classical.choice (PacketLatticeData.exists_ordinary_model_numerics _ _ _ _
    (by positivity [p.hA]) (by positivity [p.H_pos,p.hc])
    (by positivity [p.inner_pos]) p.separation)

theorem parameter_bound (w W center : ℝ) (hw : 0<w) (hW : 0<W)
    (hwW : p.H*w≤W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C) :
    ‖(p.H*w*center,p.H*w/W)‖≤p.R := by
  have hratio : 0≤w/W := (div_pos hw hW).le
  have hpad : 0≤B*(w/W) := mul_nonneg p.hB hratio
  have hcenter : 0≤w*center := by linarith [p.hc]
  have hcenterHi : w*center≤C := by linarith
  have hleft : |p.H*w*center|≤p.H*C := by
    rw [abs_of_nonneg (by nlinarith [p.H_pos])]
    nlinarith [p.H_pos]
  have hright : |p.H*w/W|≤p.H := by
    rw [abs_of_pos (div_pos (mul_pos p.H_pos hw) hW)]
    have hh : p.H*w/W≤1 := (div_le_one hW).mpr hwW
    exact hh.trans p.hH
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
  exact (max_le_max hleft hright).trans p.radius

end AnnularPacketGeometry

/-- The required geometry follows from a narrow horizontal window; all
large constants are chosen before the scale, carrier, or row families. -/
theorem exists_annular_packet_geometry (A B c C a M : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hnarrow : A≤a/4) (hsep : A/c<(3*a/(4*C)/2)/4) :
    Nonempty (AnnularPacketGeometry A B c C a M) := by
  let a0 := 3*a/(4*C)
  let b0 := (M+A)/c
  have ha0 : 0<a0 := by dsimp [a0]; positivity
  have hb0 : 0<b0 := by dsimp [b0]; positivity
  obtain ⟨H,hH⟩ := exists_gt (max 1 (max (2*a0) (6*max (2*b0) (A/c+a0/2))))
  have hH1 : 1≤H := ((le_max_left _ _).trans hH.le)
  have hHp : 0<H := zero_lt_one.trans_le hH1
  have hHa : 2*a0<H := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  have hHcover : 6*max (2*b0) (A/c+a0/2)<H :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hH)
  let R := 1+max (A+B+(M+A)/(H*c)) (max (H*C) H)
  have hR : 0<R := by
    dsimp only [R]
    have h := (le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)).trans' (le_max_right (H*C) H)
    linarith
  have hpi : (2*Real.pi*A)/(2*Real.pi*(H*c))=(A/c)/H := by
    field_simp [Real.pi_ne_zero,hHp.ne',hc.ne']
  have haH : 3*a/(4*(H*C))=a0/H := by dsimp [a0]; ring
  have hbH : (M+A)/(H*c)=b0/H := by dsimp [b0]; ring
  refine ⟨⟨H,R,hA,hB,hc,hC,ha,hM,hH1,hR,hnarrow,?_,?_,?_,?_,?_⟩⟩
  · dsimp only [R]
    linarith [le_max_left (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · dsimp only [R]
    linarith [le_max_right (A+B+(M+A)/(H*c)) (max (H*C) H)]
  · rw [haH]
    have hh : a0/H≤1/2 := (div_le_iff₀ hHp).mpr (by linarith)
    linarith
  · rw [hpi,haH,show (a0/H/2)/4=(a0/2/4)/H by ring]
    exact div_lt_div_of_pos_right hsep hHp
  · rw [hpi,haH,hbH,show 2*(b0/H)=(2*b0)/H by ring,
      show (A/c)/H+(a0/H)/2=(A/c+a0/2)/H by ring,max_div_div_right hHp.le]
    have hh := (div_lt_one hHp).mpr hHcover
    convert hh using 1
    ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
