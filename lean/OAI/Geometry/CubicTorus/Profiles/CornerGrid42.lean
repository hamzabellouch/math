import Mathlib
import OAI.Geometry.CubicTorus.Profiles.FourStarScalarGrid

namespace OAI

section
noncomputable section
namespace CubicTorus

private lemma corner_grid_42 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(3/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_4 h hl hu hd hm
  · exact corner_grid_41 h hl hu hm.le he

private lemma corner_grid_43 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_44 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (_hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_45 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(413083/243000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_46 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_44 h hl hu hd hm
  · exact corner_grid_45 h hl hu hm.le he

private lemma corner_grid_47 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/32 : ℝ) with hm|hm
  · exact corner_grid_43 h hl hm hd he
  · exact corner_grid_46 h hm.le hu hd he

private lemma corner_grid_48 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(38272/22491 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_49 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(20416/12285 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_50 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/64 : ℝ) with hm|hm
  · exact corner_grid_48 h hl hm hd he
  · exact corner_grid_49 h hm.le hu hd he

private lemma corner_grid_51 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(487136/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_52 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(33384/20825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_53 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(13/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_51 h hl hu hd hm
  · exact corner_grid_52 h hl hu hm.le he

private lemma corner_grid_54 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(3151544/1974375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_55 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(266618/170625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_56 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/64 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_54 h hl hu hd hm
  · exact corner_grid_55 h hl hu hm.le he

private lemma corner_grid_57 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/64 : ℝ) with hm|hm
  · exact corner_grid_53 h hl hm hd he
  · exact corner_grid_56 h hm.le hu hd he

private lemma corner_grid_58 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(7/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_50 h hl hu hd hm
  · exact corner_grid_57 h hl hu hm.le he

private lemma corner_grid_59 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(395648/243873 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_60 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1496/945 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_61 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/64 : ℝ) with hm|hm
  · exact corner_grid_59 h hl hm hd he
  · exact corner_grid_60 h hm.le hu hd he

private lemma corner_grid_62 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(85392032/54871425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_63 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1031272/677425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_64 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(15/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_62 h hl hu hd hm
  · exact corner_grid_63 h hl hu hm.le he

private lemma corner_grid_65 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(91/160 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2579401/1701000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_66 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/160 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(5929/4000 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_67 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/64 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/160 : ℝ) with hm|hm
  · exact corner_grid_65 h hl hu hd hm
  · exact corner_grid_66 h hl hu hm.le he

private lemma corner_grid_68 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/64 : ℝ) with hm|hm
  · exact corner_grid_64 h hl hm hd he
  · exact corner_grid_67 h hm.le hu hd he

private lemma corner_grid_69 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/32 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_61 h hl hu hd hm
  · exact corner_grid_68 h hl hu hm.le he

private lemma corner_grid_70 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/32 : ℝ) with hm|hm
  · exact corner_grid_58 h hl hm hd he
  · exact corner_grid_69 h hm.le hu hd he

private lemma corner_grid_71 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/16 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_47 h hl hu hd hm
  · exact corner_grid_70 h hl hu hm.le he

private lemma corner_grid_72 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/16 : ℝ) with hm|hm
  · exact corner_grid_42 h hl hm hd he
  · exact corner_grid_71 h hm.le hu hd he

private lemma corner_grid_73 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/8 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_3 h hl hu hd hm
  · exact corner_grid_72 h hl hu hm.le he

private lemma corner_grid_74 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (1/8 : ℝ) with hm|hm
  · exact corner_grid_2 h hl hm hd he
  · exact corner_grid_73 h hm.le hu hd he

lemma corner_grid_75 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (0/1 : ℝ)≤t) (hu : t≤(1/4 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/30 : ℝ) with hm|hm
  · exact corner_grid_1 h hl hu hd hm
  · exact corner_grid_74 h hl hu hm.le he

private lemma corner_grid_76 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_77 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (13/45 : ℝ)≤d) (he : d≤(13/36 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_78 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (_hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_79 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (_hd : (13/36 : ℝ)≤d) (he : d≤(143/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_80 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (143/360 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(82423/48600 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_81 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (143/360 : ℝ) with hm|hm
  · exact corner_grid_79 h hl hu hd hm
  · exact corner_grid_80 h hl hu hm.le he

private lemma corner_grid_82 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/36 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (7/16 : ℝ) with hm|hm
  · exact corner_grid_78 h hl hm hd he
  · exact corner_grid_81 h hm.le hu hd he

private lemma corner_grid_83 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/36 : ℝ) with hm|hm
  · exact corner_grid_77 h hl hu hd hm
  · exact corner_grid_82 h hl hu hm.le he

lemma corner_grid_84 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/45 : ℝ)≤d) (he : d≤(13/30 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (3/8 : ℝ) with hm|hm
  · exact corner_grid_76 h hl hm hd he
  · exact corner_grid_83 h hm.le hu hd he

private lemma corner_grid_85 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_86 {t d x : ℝ} (h : CornerRootData t d x)
    (_hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (_hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(7/4 : ℝ) := h.xcap
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_87 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(21309728/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_88 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(112978/70875 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_89 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_87 h hl hm hd he
  · exact corner_grid_88 h hm.le hu hd he

private lemma corner_grid_90 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_86 h hl hu hd hm
  · exact corner_grid_89 h hl hu hm.le he

private lemma corner_grid_91 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/16 : ℝ) with hm|hm
  · exact corner_grid_85 h hl hm hd he
  · exact corner_grid_90 h hm.le hu hd he

private lemma corner_grid_92 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(22554752/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_93 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(21707048/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_94 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_92 h hl hu hd hm
  · exact corner_grid_93 h hl hu hm.le he

private lemma corner_grid_95 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(480208/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_96 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(460942/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_97 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_95 h hl hu hd hm
  · exact corner_grid_96 h hl hu hm.le he

private lemma corner_grid_98 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/32 : ℝ) with hm|hm
  · exact corner_grid_94 h hl hm hd he
  · exact corner_grid_97 h hm.le hu hd he

private lemma corner_grid_99 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(17/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(370304/239841 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_100 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/64 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(89408/59409 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_101 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/64 : ℝ) with hm|hm
  · exact corner_grid_99 h hl hm hd he
  · exact corner_grid_100 h hm.le hu hd he

private lemma corner_grid_102 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(17/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(79689632/53964225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_103 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (17/64 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19209608/13367025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_104 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (17/64 : ℝ) with hm|hm
  · exact corner_grid_102 h hl hm hd he
  · exact corner_grid_103 h hm.le hu hd he

private lemma corner_grid_105 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(9/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_101 h hl hu hd hm
  · exact corner_grid_104 h hl hu hm.le he

private lemma corner_grid_106 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(19/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9856/6723 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_107 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/64 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1888/1323 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_108 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/64 : ℝ) with hm|hm
  · exact corner_grid_106 h hl hm hd he
  · exact corner_grid_107 h hm.le hu hd he

private lemma corner_grid_109 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(19/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(73987232/52943625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_110 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (19/64 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(404182/297675 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_111 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (19/64 : ℝ) with hm|hm
  · exact corner_grid_109 h hl hm hd he
  · exact corner_grid_110 h hm.le hu hd he

private lemma corner_grid_112 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (9/32 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_108 h hl hu hd hm
  · exact corner_grid_111 h hl hu hm.le he

private lemma corner_grid_113 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (9/32 : ℝ) with hm|hm
  · exact corner_grid_105 h hl hm hd he
  · exact corner_grid_112 h hm.le hu hd he

private lemma corner_grid_114 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(5/16 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_98 h hl hu hd hm
  · exact corner_grid_113 h hl hu hm.le he

private lemma corner_grid_115 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(19703552/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_116 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18855848/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_117 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_115 h hl hu hd hm
  · exact corner_grid_116 h hl hu hm.le he

private lemma corner_grid_118 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(377/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(14836/10125 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_119 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (377/720 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(198071/141750 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_120 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (377/720 : ℝ) with hm|hm
  · exact corner_grid_118 h hl hu hd hm
  · exact corner_grid_119 h hl hu hm.le he

private lemma corner_grid_121 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(13/24 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_117 h hl hm hd he
  · exact corner_grid_120 h hm.le hu hd he

private lemma corner_grid_122 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(21/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(319616/230265 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_123 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/64 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(76736/56889 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_124 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/64 : ℝ) with hm|hm
  · exact corner_grid_122 h hl hm hd he
  · exact corner_grid_123 h hm.le hu hd he

private lemma corner_grid_125 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(21/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(9754976/7401375 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_126 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (21/64 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(16358408/12800025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_127 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (21/64 : ℝ) with hm|hm
  · exact corner_grid_125 h hl hm hd he
  · exact corner_grid_126 h hm.le hu hd he

private lemma corner_grid_128 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(11/32 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_124 h hl hu hd hm
  · exact corner_grid_127 h hl hu hm.le he

private lemma corner_grid_129 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(23/64 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(294272/224721 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_130 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/64 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(80/63 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_131 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(403/720 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/64 : ℝ) with hm|hm
  · exact corner_grid_129 h hl hm hd he
  · exact corner_grid_130 h hm.le hu hd he

private lemma corner_grid_132 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(23/64 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(62582432/50562225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_133 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (23/64 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(169691/141750 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_134 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (403/720 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (23/64 : ℝ) with hm|hm
  · exact corner_grid_132 h hl hm hd he
  · exact corner_grid_133 h hm.le hu hd he

private lemma corner_grid_135 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (11/32 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (403/720 : ℝ) with hm|hm
  · exact corner_grid_131 h hl hu hd hm
  · exact corner_grid_134 h hl hu hm.le he

private lemma corner_grid_136 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/24 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (11/32 : ℝ) with hm|hm
  · exact corner_grid_128 h hl hm hd he
  · exact corner_grid_135 h hm.le hu hd he

private lemma corner_grid_137 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (5/16 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (13/24 : ℝ) with hm|hm
  · exact corner_grid_121 h hl hu hd hm
  · exact corner_grid_136 h hl hu hm.le he

private lemma corner_grid_138 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (91/180 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (5/16 : ℝ) with hm|hm
  · exact corner_grid_114 h hl hm hd he
  · exact corner_grid_137 h hm.le hu hd he

lemma corner_grid_139 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (1/4 : ℝ)≤t) (hu : t≤(3/8 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(26/45 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (91/180 : ℝ) with hm|hm
  · exact corner_grid_91 h hl hu hd hm
  · exact corner_grid_138 h hl hu hm.le he

private lemma corner_grid_140 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(2216192/1346625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_141 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(514448/326025 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_142 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_140 h hl hm hd he
  · exact corner_grid_141 h hm.le hu hd he

private lemma corner_grid_143 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(13/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(18458528/12119625 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_144 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(4258232/2934225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_145 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(50138/36225 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_146 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (13/32 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_144 h hl hu hd hm
  · exact corner_grid_145 h hl hu hm.le he

private lemma corner_grid_147 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (13/32 : ℝ) with hm|hm
  · exact corner_grid_143 h hl hm hd he
  · exact corner_grid_146 h hm.le hu hd he

lemma corner_grid_148 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (3/8 : ℝ)≤t) (hu : t≤(7/16 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (169/360 : ℝ) with hm|hm
  · exact corner_grid_142 h hl hu hd hm
  · exact corner_grid_147 h hl hu hm.le he

private lemma corner_grid_149 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(1899392/1258425 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_150 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (15/32 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(27203/18900 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_151 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(1/2 : ℝ))
    (hd : (13/30 : ℝ)≤d) (he : d≤(169/360 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt t (15/32 : ℝ) with hm|hm
  · exact corner_grid_149 h hl hm hd he
  · exact corner_grid_150 h hm.le hu hd he

private lemma corner_grid_152 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(39/80 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(15607328/11325825 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

private lemma corner_grid_153 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (39/80 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  have hx : x≤(26136/19975 : ℝ) := corner_root_interval_bound h.t0 h.d0 h.x0 h.root
    hl hu hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact corner_box_strict h.t0 h.d0 h.x0 hu he hx (by norm_num)

lemma corner_grid_154 {t d x : ℝ} (h : CornerRootData t d x)
    (hl : (7/16 : ℝ)≤t) (hu : t≤(15/32 : ℝ))
    (hd : (169/360 : ℝ)≤d) (he : d≤(91/180 : ℝ)) :
    d+(t^2+(t+x*d)^2)/Real.pi<1 := by
  rcases le_or_gt d (39/80 : ℝ) with hm|hm
  · exact corner_grid_152 h hl hu hd hm
  · exact corner_grid_153 h hl hu hm.le he

end CubicTorus
end
end

end OAI
